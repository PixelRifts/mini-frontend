# mini-frontend
A highly minimal compiler frontend, useful for experimentation

## Testing

1. Clone the Repository
2. Run the build script (It exists for windows, but not for linux. The code should work as-is though, there's just no buildscript for it)
3. Run the exe with your code file as the first argument

## Structure
Note: Important Declarations in Parens.\
\
Lexing: Pretty Basic, nothing to write home about. (lexer.h: TokenType, Token, Lexer)\
\
Parsing: Simple Pratt Parsing, Jai/Odin/Pascal like syntax. (parser.h: NodeType, ASTNode, ConstantValue, Parser)\
\
Checking: Due to wanting to support out-of-order declarations the Checking is split into 2 Phases: Outer and Inner\
The Outer Check does not check statements within statements/expressions (So sub-statements in a {} scope are not checked here). But it does figure out the expression type of all expressions.\
The Inner Check does the recursive check into sub-statements within statements/expressions.\
(checker.h: TypeKind, ValueType, Symbol, Checker)\

## TODOs
- Some code samples.
