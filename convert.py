import sys

class Convert:
    def __init__(self, sourcefile, targetfile):
        self.s = sourcefile
        self.t = targetfile
        self.info_dict = self.build_info_dict()
        self.command_dict = self.build_command_dict()

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
            if not c or c.isspace():
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
        res = {}
        while True:
            c = self.s.read(1)
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                break
            elif c == '(':
                key = self.read_word()
                val = self.read_until(')').strip()
                res[key] = val
            elif c.isspace():
                pass # skipping whitepace
            else:
                raise ValueError('unexpected ' + c)
        return res

    def convert_name(self, s):
        # TODO this might result in name clashes, maintain dict and generate fresh name
        # if needed
        return s.replace('!', '_').replace('.', '_')

    def datatype(self):
        while True:
            c = self.s.read()
            if not c:
                raise ValueError('not enough input')
            if c == ')':
                break
            elif c == '(':
                self.constructor()
            elif c.isspace():
                pass
            else:
                raise ValueError('unexpected ' + c)

    def declare_datatypes(self):
        self.read_until('(')
        name2arity_raw = self.read_dict()
        print(name2arity_raw)
        name2arity = { self.convert_name(k): int(v) for (k, v) in name2arity_raw.items() }
        print(name2arity)


    def build_command_dict(self):
        return {
            'set-info': self.set_info,
            'set-logic': self.set_logic,
            'declare-datatypes': self.declare_datatypes,
            }

    def command(self):
        command_name = self.read_word()
        self.command_dict[command_name]()

    def run(self):
        while True:
            c = self.s.read(1)
            if not c:
                # End of file
                break
            if c == '(':
                self.command()

if __name__ == "__main__":
    infile = open(sys.argv[1])
    outfile = sys.stdout
    c = Convert(infile, outfile)
    c.run()
