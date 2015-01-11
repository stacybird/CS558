#! /usr/bin/env python3

def hi(s):
    print ('Hello '+ s + '!')

# support invocation from the command line
if __name__ == "__main__":
    import sys
    hi(sys.argv[1])
