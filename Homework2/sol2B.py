#! /usr/bin/env python3

#   Homework #2  Stacy Watts   swatts@pdx.edu
# ----------------------------------------------------------------------------
# Abstract Syntax, Printing, Evaluation
# ----------------------------------------------------------------------------
#
# Each kind of expression is a distinct class.
#

class VarExp:
    def __init__(self, x):
       self.x = x

    def toString(self):
       return self.x

    def eval(self, env):
       v = env.get(self.x)
       if (v == None): 
           # variable is undefined; initialize it to 0
           v = 0
           env[self.x] = v
       return v

class IntExp:
    def __init__(self, i):
        self.i = i

    def toString(self):
        return str(self.i)

    def eval(self, env):
        return self.i

class AsgnExp:
    def __init__(self, x, e):
        self.x = x
        self.e = e

    def toString(self):
        return "(:= " + self.x + " " + self.e.toString() + ")"

    def eval(self, env):
        v = self.e.eval(env)
        env[self.x] = v
        return v


class WhileExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):        
        return "(while " + self.e1.toString() + " " + self.e2.toString() + ")"

    def eval(self, env):
        while (self.e1.eval(env) != 0):
            self.e2.eval(env)
        return 0


class ForExp:
    def __init__(self, x, e1, e2, e3):
        self.x  = x
        self.e1 = e1
        self.e2 = e2
        self.e3 = e3

    def toString(self):        
        return "(for " + self.x + " " + self.e1.toString() + " " + self.e2.toString() + " " + self.e3.toString() + ")"

    def eval(self, env):
        v1 = self.e1.eval(env)
        env[self.x] = v1
        v2 = self.e2.eval(env)
        x = env.get(self.x)
        while (x <= v2):
          self.e3.eval(env)
          x = env.get(self.x) + 1
          env[self.x] = x
        return 0


class IfExp:
    def __init__(self, e1, e2, e3):
        self.e1 = e1
        self.e2 = e2
        self.e3 = e3

    def toString(self):
        return "(if " + self.e1.toString() + " " + self.e2.toString() + " " + self.e3.toString() + ")"
        
    def eval(self, env):
        if (self.e1.eval(env) != 0):
            return self.e2.eval(env)
        else:
            return self.e3.eval(env)

class WriteExp:
    def __init__(self, e):
        self.e = e

    def toString(self):
        return "(write " + self.e.toString() + ")"

    def eval(self, env):
        v = self.e.eval(env)
        print(v)
        return v


class BlockExp:
    def __init__(self, es):
        self.es = es

    def toString(self):
        return "(block " + " ".join([e.toString() for e in self.es]) + ")"

    def eval(self, env):
        v = 0
        for e in self.es:
            v = e.eval(env)
        return v

class AddExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(+ ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self, env):
        return self.e1.eval(env) + self.e2.eval(env)

class SubExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(- ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self, env):
        return self.e1.eval(env) - self.e2.eval(env)

class MulExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(* ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self, env):
        return self.e1.eval(env) * self.e2.eval(env)

class DivExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(/ ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self, env):
        return self.e1.eval(env) // self.e2.eval(env) # gives integer result

class LeqExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(<= ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self, env):
        return int(self.e1.eval(env) <= self.e2.eval(env))

# ----------------------------------------------------------------------------
# Lexical Analysis and Parsing
# ----------------------------------------------------------------------------
#

class ParseError(Exception):
    def __init__(self, reason, lineno):
        self.reason = reason
        self.lineno = lineno
    
# Lexical tokens

# Token type (ttype) codes
NUM = 0
OPER = 1
ID = 2
LP = 3
RP = 4
EOF = 5

class Token:
    def __init__(self, ttype, lineno):
        self.ttype = ttype
        self.lineno = lineno

def mkNUM(num, lineno):
    t = Token(NUM, lineno)
    t.num = num
    return t

def mkOPER(oper, lineno):
    t = Token(OPER, lineno)
    t.oper = oper
    return t

def mkID(s, lineno):
    t = Token(ID, lineno)
    t.s = s
    return t

def mkLP(lineno):
    return Token(LP, lineno)

def mkRP(lineno):
    return Token(RP, lineno)

def mkEOF(lineno):
    return Token(EOF, lineno)


def is_whitespace(c):
    return c.isspace()

def is_num_char(c):
    return c.isdigit()

def is_oper_char(c):
    return c in '+-*/<=:='

def is_id_char(c):
    return c.isalpha()

# Lexical analysis

# Streams supporting the "putting back" of one character
class PushbackStream:
    def __init__(self,stream):
        self.stream = stream
        self.cache = None

    def readc(self):
        if self.cache == None:
            return self.stream.read(1)
        else:
            c = self.cache
            self.cache = None
            return c

    def unreadc(self,c):
        self.cache = c

# Token generator
class Tokenizer:
    def __init__(self, stream):
        self.stream = PushbackStream(stream)
        self.lineno = 1
        self.cache = None

    def next(self):
        result = self.cache
        self.cache = None
        comment_level = 0
        while (result == None):
             c = self.stream.readc()
             if c == '':
                 if comment_level > 0:
                     raise ParseError("Unmatched open comment", self.lineno)
                 else:
                     result = mkEOF(self.lineno)
             elif c == '\n':
                 self.lineno += 1
                 continue
             elif c == '{':
                 c = self.stream.readc()
                 if c == '-':
                     comment_level += 1
                 else:
                     raise ParseError("Open comment brace without '-'", self.lineno)
                 continue
             elif (c == '-'):
                 c = self.stream.readc()
                 if not(c == '}') and comment_level == 0 :
                      s = '-'
                      while is_oper_char(c):
                         s = s + c
                         c = self.stream.readc()
                      self.stream.unreadc(c)
                      return mkOPER(s, self.lineno) 
                 elif not(c == '}'):
                    continue  
                 else: 
                   if comment_level > 0:
                        comment_level -= 1
                        continue
                   else:    
                       raise ParseError("Close comment -} without preceding matching open comment {-", self.lineno)                                          
             elif c == '}':
                raise ParseError("Expecting close comment -} but found }", self.lineno)
             elif comment_level > 0:
                 continue
             elif is_whitespace(c):
                 continue
             elif c == '(':
                 result = mkLP(self.lineno)
             elif c == ')':
                 result = mkRP(self.lineno)
             elif is_num_char(c):
                 s = c
                 c = self.stream.readc()
                 while (is_num_char(c)):
                     s = s + c
                     c = self.stream.readc()
                 self.stream.unreadc(c)
                 result = mkNUM(int(s), self.lineno)
             elif is_oper_char(c):
                 s = c
                 c = self.stream.readc()
                 while is_oper_char(c):
                     s = s + c
                     c = self.stream.readc()
                 self.stream.unreadc(c)
                 result = mkOPER(s, self.lineno)
             elif is_id_char(c):
                 s = c
                 c = self.stream.readc()
                 while is_id_char(c):
                     s = s + c
                     c = self.stream.readc()
                 self.stream.unreadc(c)
                 result = mkID(s, self.lineno)
             else:
                 raise ParseError('Invalid character:' + repr(c), self.lineno)
        return result

    def putback(self, tok):
        self.cache = tok

# Recursive-descent parsing

# Parse variable
def parse_var(tokens):
    tok = tokens.next()
    if (tok.ttype == ID):
        return tok.s
    else:
        raise ParseError('Missing variable name', tok.lineno)

# Parse expression
def parse_exp(tokens):
    tok = tokens.next()
    if tok.ttype == NUM:
        result = IntExp(tok.num)
    elif tok.ttype == ID:
        result = VarExp(tok.s)
    elif tok.ttype == LP:
        tok = tokens.next()
        if tok.ttype == ID:
            keywd = tok.s
            if keywd == "while":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = WhileExp(e1, e2)
            elif keywd == "for":
                x = parse_var(tokens)
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                e3 = parse_exp(tokens)
                result = ForExp(x, e1, e2, e3)
            elif keywd == "if":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                e3 = parse_exp(tokens)
                result = IfExp(e1, e2, e3)
            elif keywd == "write":
                e = parse_exp(tokens)
                result = WriteExp(e)
            elif keywd == "block":
                es = []
                tok = tokens.next()
                while (tok.ttype != RP):
                    tokens.putback(tok)
                    es.append(parse_exp(tokens))
                    tok = tokens.next()
                tokens.putback(tok)
                result = BlockExp(es)
        elif tok.ttype == OPER:
            oper = tok.oper
            if oper == ":=":
                v = parse_var(tokens)
                e = parse_exp(tokens)
                result = AsgnExp(v,e)
            elif oper == "+":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = AddExp(e1, e2)
            elif oper == "-": 
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = SubExp(e1, e2)
            elif oper == "*":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = MulExp(e1, e2)
            elif oper == "/":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = DivExp(e1, e2)
            elif oper == "<=":
                e1 = parse_exp(tokens)
                e2 = parse_exp(tokens)
                result = LeqExp(e1, e2)
            else:
                raise ParseError("Invalid operator:" + repr(oper), tok.lineno)
        else:
            raise ParseError("Missing or invalid expression", tok.lineno)
        tok = tokens.next()
        if tok.ttype != RP:
            raise ParseError("Missing )", tok.lineno)
    else:
        raise ParseError("Missing or invalid expression", tok.lineno)
    return result

# Parse program
def parse(stream):
    tokens = Tokenizer(stream)
    exp = parse_exp(tokens)
    tok = tokens.next()
    if tok.ttype != EOF:
        raise ParseError("Extraneous characters at end of program", tok.lineno)
    return exp


# ----------------------------------------------------------------------------
# Top-level interpreter 
# ----------------------------------------------------------------------------

def interp(filename):
    with open (filename, 'r') as f:
        try:
            exp = parse(f)
        except ParseError as err:     
            print ("Parse failed: Line", str(err.lineno), ":", err.reason)
        else:
            print ('Expression:', exp.toString())
            result = exp.eval({})
            print ('Evaluates to:', result)

# support invocation from the command line
if __name__ == "__main__":
    import sys
    interp(sys.argv[1])

