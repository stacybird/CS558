# Homework 1  Stacy Watts   swatts@pdx.edu
#! /usr/bin/env python3

# ----------------------------------------------------------------------------
# Abstract Syntax, Printing, Evaluation
# ----------------------------------------------------------------------------
#
# Each kind of expression is a distinct class.
#

class IntExp:
    def __init__(self, i):
        self.i = i

    def toString(self):
        return str(self.i)

    def eval(self):
        return self.i


class AddExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(+ ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self):
        v1 = self.e1.eval()
        v2 = self.e2.eval()
        return v1 + v2

class SubExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(- ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self):
        v1 = self.e1.eval()
        v2 = self.e2.eval()
        return v1 - v2

class MulExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(* ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self):
        v1 = self.e1.eval()
        v2 = self.e2.eval()
        return v1 * v2

class DivExp:
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def toString(self):
        return '(/ ' + self.e1.toString() + " " + self.e2.toString() + ')'  

    def eval(self):
        v1 = self.e1.eval()
        v2 = self.e2.eval()
        return v1 // v2  # gives integer result

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
LP = 2
RP = 3
EOF = 4

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

def mkLP(lineno):
    return Token(LP, lineno)

def mkRP(lineno):
    return Token(RP, lineno)

def mkEOF(lineno):
    return Token(EOF, lineno)


def is_digit(c):
    return c.isdigit()

def is_whitespace(c):
    return c.isspace()

def is_oper_char(c):
    return c in '+-*/'

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

    def next(self):
         comment_level = 0
         while True:
             c = self.stream.readc()
             if c == '':
                 if comment_level > 0:
                     raise ParseError("Unmatched open comment", self.lineno)
                 else:
                     return mkEOF(self.lineno)
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
                 return mkLP(self.lineno)
             elif c == ')':
                 return mkRP(self.lineno)
             elif is_digit(c):
                 s = c
                 c = self.stream.readc()
                 while (c.isdigit()):
                     s = s + c
                     c = self.stream.readc()
                 self.stream.unreadc(c)
                 return mkNUM(int(s), self.lineno)
             elif is_oper_char(c):
                 s = c
                 c = self.stream.readc()
                 while is_oper_char(c):
                     s = s + c
                     c = self.stream.readc()
                 self.stream.unreadc(c)
                 return mkOPER(s, self.lineno)
             else:
                 raise ParseError('Invalid character:' + repr(c), self.lineno)
    
# Recursive-descent parsing

# Parse expression
def parse_exp(tokens):
    result = None
    tok = tokens.next()
    if tok.ttype == NUM:
        result = IntExp(tok.num)
    elif tok.ttype == LP:
        tok = tokens.next()
        if tok.ttype == OPER:
            oper = tok.oper
            e1 = parse_exp(tokens)
            e2 = parse_exp(tokens)
            if oper == "+":
                result = AddExp(e1, e2)
            elif oper == "-": 
                result = SubExp(e1, e2)
            elif oper == "*":
                result = MulExp(e1, e2)
            elif oper == "/":
                result = DivExp(e1, e2)
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
            result = exp.eval()
            print ('Evaluates to:', result)

# support invocation from the command line
if __name__ == "__main__":
    import sys
    interp(sys.argv[1])

