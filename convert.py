import sys

class Convert:
    def __init__(self, sourcefile, targetfile):
        self.s = sourcefile
        self.t = targetfile
        self.info_dict = self.build_info_dict()
        self.command_dict = self.build_command_dict()
        self.hyp_counter = 0

    def read_word(self):
        c = ''
        # skip whitespace
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('word expected, but EOF found')
            if not c.isspace():
                break
        res = ''
        while True:
            if not c or c.isspace() or c == ')' or c == '(':
                break
            res += c
            c = self.s.read(1)
        return res

    def read_until(self, expect):
        w = self.s.read(len(expect))
        res = w
        if not w:
            raise ValueError('not enough input')
        while True:
            if w == expect:
                break
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            w = w[1:] + c
            res += c
        return res[:-len(expect)]


    def build_info_dict(self):
        return {
            ':smt-lib-version': self.info_smt_lib_version,
            ':source': self.info_source,
            ':license': self.info_license,
            ':category': self.info_category,
            ':status': self.info_status
            }

    def info_smt_lib_version(self):
        self.t.write(self.read_until(')'))

    def info_source(self):
        self.read_until('|')
        self.t.write(self.read_until('|)'))

    def info_license(self):
        self.read_until('"')
        self.t.write(self.read_until('")'))

    def info_category(self):
        self.read_until('"')
        self.t.write(self.read_until('")'))

    def info_status(self):
        self.t.write(self.read_until(')'))

    def set_info(self):
        self.t.write('(*set-info ')
        info_name = self.read_word()
        self.t.write(info_name)
        self.t.write(' ')
        self.info_dict[info_name]()
        self.t.write('*)\n')

    def set_logic(self):
        self.t.write('(*set-logic ')
        logic_name = self.read_until(')')
        self.t.write(logic_name)
        self.t.write('*)\n')

    def read_dict(self):
        res = []
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                break
            elif c == '(':
                key = self.read_word()
                val = self.read_until(')').strip()
                res.append((key, val))
            elif c.isspace():
                pass # skipping whitepace
            else:
                raise ValueError('unexpected ' + c)
        return res

    def convert_name(self, s):
        # TODO this might result in name clashes, maintain dict and generate fresh name
        # if needed
        return s.replace('!', '_').replace('.', '_')

    def process_list(self, process_elem, args=None):
        i = 0
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                break
            elif c == '(':
                if args:
                    process_elem(i, args[i])
                else:
                    process_elem(i)
                i += 1
            elif c.isspace():
                pass
            else:
                raise ValueError('unexpected ' + c)

    # reads one more closing parenthesis than opening parentheses
    def read_until_cl_paren(self):
        res = ''
        depth = 0
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            if c == ')' and depth == 0:
                break
            elif c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            res += c
        return res

    def constructor_arg(self, i):
        name = self.read_word()
        self.t.write('(')
        self.t.write(self.convert_name(name))
        self.t.write(' : ')
        sort = self.read_until_cl_paren()
        self.t.write(self.convert_name(sort))
        self.t.write(')')

    def constructor(self, i):
        name = ''
        read_closing = False
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                read_closing = True
                break
            elif c.isspace():
                break
            name += c
        self.t.write('  | ')
        self.t.write(self.convert_name(name))
        if not read_closing:
            self.process_list(self.constructor_arg)
        self.t.write('\n')

    def datatype(self, i, nameAndArity):
        if i == 0:
            self.t.write('Inductive ')
        else:
            self.t.write('with ')
        self.t.write(nameAndArity[0])
        self.t.write(' := \n')
        self.process_list(self.constructor)

    def datatypes(self, name2arity):
        self.process_list(self.datatype, name2arity)
        self.t.write('.\n')

    def declare_datatypes(self):
        self.read_until('(')
        name2arity_raw = self.read_dict()
        name2arity = [ (self.convert_name(k), int(v)) for (k, v) in name2arity_raw ]
        self.read_until('(')
        self.datatypes(name2arity)

    def process_fun_decl_arg_sort_list(self):
        while True:
            c = self.s.read(1)
            read_closing = False
            sort = None
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                break
            elif c.isspace():
                pass
            elif c == '(':
                sort = self.read_until_cl_paren()
            else:
                sort = c
                while True:
                    c = self.s.read(1)
                    if not c:
                        raise ValueError('not enough input')
                    if c == ')':
                        read_closing = True
                        break
                    elif c.isspace():
                        break
                    sort += c
            if sort:
                self.t.write(self.convert_name(sort))
                self.t.write(' -> ')
            if read_closing:
                break

    def declare_fun(self):
        name = self.read_word()
        self.t.write('Variable ')
        self.t.write(self.convert_name(name))
        self.t.write(' : ')
        self.read_until('(')
        self.process_fun_decl_arg_sort_list()
        rettype = self.read_until_cl_paren().strip()
        self.t.write(self.convert_name(rettype))
        self.t.write('.\n')

    def asssert(self):
        f = self.read_until_cl_paren()
        f2 = self.convert_name(f).replace('(*', '( *')
        self.t.write('Hypothesis A')
        self.t.write(str(self.hyp_counter))
        self.hyp_counter += 1
        self.t.write(' : ')
        self.t.write(f2)
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
        command_name = self.read_word()
        self.command_dict[command_name]()

    def run(self):
        self.t.write('Section Test.\n')
        while True:
            c = self.s.read(1)
            if not c:
                # End of file
                break
            if c == '(':
                self.command()
        self.t.write('End Test.\n')

if __name__ == "__main__":
    filepath = sys.argv[1]
    if filepath[-5:] != '.smt2':
        raise ValueError('unexpected format')
    filepath = filepath[:-5]
    infile = open(filepath + '.smt2')
    outfile = open(filepath + '.v', 'w')
    c = Convert(infile, outfile)
    c.run()
