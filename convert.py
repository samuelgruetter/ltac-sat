import sys

class Convert:
    def __init__(self, sourcefile, targetfile):
        self.s = sourcefile
        self.t = targetfile
        self.info_dict = self.build_info_dict()
        self.command_dict = self.build_command_dict()
        self.hyp_counter = 0
        self.fwd()

    def fwd(self):
        self.cur = self.s.read(1)

    def consume(self, text):
        w = self.s.read(len(text))
        if not w:
            raise ValueError(text + ' expected, but EOF found')
        found = self.cur + w[:-1]
        if found != text:
            raise ValueError(text + ' expected, but ' + found + ' found')
        self.cur = w[-1]

    def read_until(self, predicate):
        res = ''
        while self.cur and not predicate(self.cur):
            res += self.cur
            self.fwd()
        return res

    def skip_whitespace(self):
        self.read_until(lambda c: not c.isspace())

    def read_word(self):
        self.skip_whitespace()
        if not self.cur:
            raise ValueError('word expected, but EOF found')
        return self.read_until(lambda c: c == '(' or c == ')' or c.isspace())

    def read_quoted_string(self):
        self.read_until(lambda c: c == '"')
        self.consume('"')
        res = self.read_until(lambda c: c == '"')
        self.consume('"')
        return res

    def read_multiline_string(self):
        self.read_until(lambda c: c == '|')
        self.consume('|')
        res = self.read_until(lambda c: c == '|')
        self.consume('|')
        return res

    def info_smt_lib_version(self):
        self.t.write(self.read_word())

    def info_source(self):
        self.t.write('|')
        self.t.write(self.read_multiline_string())
        self.t.write('|')

    def info_license(self):
        self.t.write('"')
        self.t.write(self.read_quoted_string())
        self.t.write('"')

    def info_category(self):
        self.t.write('"')
        self.t.write(self.read_quoted_string())
        self.t.write('"')

    def info_status(self):
        self.t.write(self.read_word())

    def build_info_dict(self):
        return {
            ':smt-lib-version': self.info_smt_lib_version,
            ':source': self.info_source,
            ':license': self.info_license,
            ':category': self.info_category,
            ':status': self.info_status
            }

    def set_info(self):
        self.t.write('(*set-info ')
        info_name = self.read_word()
        self.t.write(info_name)
        self.t.write(' ')
        self.info_dict[info_name]()
        self.t.write('*)\n')

    def set_logic(self):
        self.t.write('(*set-logic ')
        logic_name = self.read_word()
        self.t.write(logic_name)
        self.t.write('*)\n')

    def read_list(self, read_elem):
        res = []
        self.consume('(')
        while True:
            self.skip_whitespace()
            if not self.cur:
                raise ValueError('")" or list elem expected, but EOF found')
            if self.cur == ')':
                break
            res.append(read_elem())
        self.consume(')')
        return res

    def read_name_and_arity(self):
        self.consume('(')
        name = self.convert_name(self.read_word())
        arity = int(self.read_word())
        self.skip_whitespace()
        self.consume(')')
        return (name, arity)

    def convert_name(self, s):
        # TODO this might result in name clashes, maintain dict and generate fresh name
        # if needed
        return s.replace('!', '_').replace('.', '_')

    # does not consume surrounding parentheses
    def process_list(self, process_elem, args=None):
        i = 0
        while True:
            self.skip_whitespace()
            if not self.cur:
                raise ValueError('")" or list elem expected, but EOF found')
            if self.cur == ')':
                break
            if args:
                process_elem(i, args[i])
            else:
                process_elem(i)
            i += 1

    def sort(self, needs_paren=True):
        self.skip_whitespace()
        if self.cur == '(':
            self.consume('(')
            if needs_paren:
                self.t.write('(')
            head = self.read_word()
            if head == '_':
                head = self.read_word()
            self.t.write(head)
            while True:
                self.skip_whitespace()
                if not self.cur:
                    raise ValueError('")" or list elem expected, but EOF found')
                if self.cur == ')':
                    break
                self.t.write(' ')
                self.sort()
            self.consume(')')
            if needs_paren:
                self.t.write(')')
        else:
            name = self.convert_name(self.read_word())
            self.t.write(name)

    def constructor_arg(self, i):
        self.consume('(')
        name = self.read_word()
        self.t.write('(')
        self.t.write(self.convert_name(name))
        self.t.write(' : ')
        self.sort(needs_paren=False)
        self.consume(')')
        self.t.write(')')

    def constructor(self, i):
        self.consume('(')
        name = self.convert_name(self.read_word())
        self.skip_whitespace()
        self.t.write('  | ')
        self.t.write(name)
        self.process_list(self.constructor_arg)
        self.consume(')')
        self.t.write('\n')

    def datatype(self, i, nameAndArity):
        if i == 0:
            self.t.write('Inductive ')
        else:
            self.t.write('with ')
        self.t.write(nameAndArity[0])
        self.t.write(' := \n')
        self.consume('(')
        self.process_list(self.constructor)
        self.consume(')')

    def datatypes(self, name2arity):
        self.skip_whitespace()
        self.consume('(')
        self.process_list(self.datatype, name2arity)
        self.consume(')')
        self.t.write('.\n')

    def declare_datatypes(self):
        self.skip_whitespace()
        name2arity = self.read_list(self.read_name_and_arity)
        self.datatypes(name2arity)

    def sort_followed_by_arrow(self, i):
        self.sort(needs_paren=False)
        self.t.write(' -> ')

    def declare_fun(self):
        name = self.read_word()
        self.t.write('Variable ')
        self.t.write(self.convert_name(name))
        self.t.write(' : ')
        self.skip_whitespace()
        # list of arg types
        self.consume('(')
        self.process_list(self.sort_followed_by_arrow)
        self.consume(')')
        self.skip_whitespace()
        # return type
        self.sort(needs_paren=False)
        self.t.write('.\n')

    infix_ops = {
        '*': '*',
        '+': '+',
        '=': '=',
        'and': '/\\',
        'or': '\\/',
    }

    def expr(self, needs_paren=True):
        self.skip_whitespace()
        if self.cur == '(':
            self.consume('(')
            if needs_paren:
                self.t.write('(')
            op = self.read_word()
            if op in self.infix_ops:
                sep = ' ' + self.infix_ops[op] + ' '
            else:
                sep = ' '
                self.t.write(self.convert_name(op))
                self.t.write(' ')
            while True:
                self.expr()
                self.skip_whitespace()
                if not self.cur:
                    raise ValueError('")" or expr expected, but EOF found')
                if self.cur == ')':
                    break
                self.t.write(sep)
            self.consume(')')
            if needs_paren:
                self.t.write(')')
        else:
            name = self.convert_name(self.read_word())
            self.t.write(name)

    def asssert(self):
        self.t.write('Hypothesis A')
        self.t.write(str(self.hyp_counter))
        self.hyp_counter += 1
        self.t.write(' : ')
        self.expr()
        self.t.write('.\n')

    def check_sat(self):
        self.t.write('Theorem unsat: False.\n')
        self.t.write('Proof.\n')
        self.t.write('\n')
        self.t.write('Abort.\n')

    def exxit(self):
        pass

    def build_command_dict(self):
        return {
            'set-info': self.set_info,
            'set-logic': self.set_logic,
            'declare-datatypes': self.declare_datatypes,
            'declare-fun': self.declare_fun,
            'assert': self.asssert,
            'check-sat': self.check_sat,
            'exit': self.exxit,
            }

    def command(self):
        self.consume('(')
        command_name = self.read_word()
        self.command_dict[command_name]()
        self.skip_whitespace()
        self.consume(')')

    def run(self):
        self.t.write('Section Test.\n')
        while True:
            self.skip_whitespace()
            if not self.cur:
                # End of file
                break
            self.command()
        self.t.write('End Test.\n')

if __name__ == "__main__":
    infile = sys.stdin
    outfile = sys.stdout
    if len(sys.argv) >= 2:
        infile = open(sys.argv[1])
    if len(sys.argv) >= 3:
        outfile = open(sys.argv[2])
    c = Convert(infile, outfile)
    c.run()
