/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_C_GRAM_H_INCLUDED
# define YY_YY_C_GRAM_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    IDENT = 258,
    STRING = 259,
    FIELD_NAME = 260,
    TYPEDEF_NAME = 261,
    TAG = 262,
    CHAR_CONST = 263,
    INUM = 264,
    RNUM = 265,
    COMMENT = 266,
    PP_DEFINE = 267,
    INVALID = 268,
    AUTO = 269,
    BREAK = 270,
    CASE = 271,
    CHAR = 272,
    CONST = 273,
    CONT = 274,
    DEFLT = 275,
    DO = 276,
    DOUBLE = 277,
    ELSE = 278,
    ENUM = 279,
    EXTRN = 280,
    IF = 281,
    FOR = 282,
    FLOAT = 283,
    GOTO = 284,
    INT = 285,
    LONG = 286,
    REGISTR = 287,
    RETURN = 288,
    SHORT = 289,
    SGNED = 290,
    STATIC = 291,
    STRUCT = 292,
    SWITCH = 293,
    TYPEDEF = 294,
    UNION = 295,
    UNSGNED = 296,
    VOID = 297,
    VOLATILE = 298,
    WHILE = 299,
    PLUS_EQ = 300,
    MINUS_EQ = 301,
    STAR_EQ = 302,
    DIV_EQ = 303,
    MOD_EQ = 304,
    B_NOT_EQ = 305,
    B_AND_EQ = 306,
    B_OR_EQ = 307,
    B_XOR_EQ = 308,
    L_SHIFT_EQ = 309,
    R_SHIFT_EQ = 310,
    EQUAL = 311,
    LESS_EQ = 312,
    GRTR_EQ = 313,
    NOT_EQ = 314,
    RPAREN = 315,
    RBRCKT = 316,
    LBRACE = 317,
    RBRACE = 318,
    SEMICOLON = 319,
    COMMA = 320,
    ELLIPSIS = 321,
    LB_SIGN = 322,
    DOUB_LB_SIGN = 323,
    BACKQUOTE = 324,
    AT = 325,
    DOLLAR = 326,
    CPP_INCLUDE = 327,
    CPP_DEFINE = 328,
    CPP_LINE = 329,
    COMMA_OP = 330,
    EQ = 331,
    ASSIGN = 332,
    QUESTMARK = 333,
    COLON = 334,
    COMMA_SEP = 335,
    OR = 336,
    AND = 337,
    B_OR = 338,
    B_XOR = 339,
    B_AND = 340,
    COMP_EQ = 341,
    COMP_ARITH = 342,
    LESS = 343,
    GRTR = 344,
    L_SHIFT = 345,
    R_SHIFT = 346,
    PLUS = 347,
    MINUS = 348,
    STAR = 349,
    DIV = 350,
    MOD = 351,
    CAST = 352,
    UNARY = 353,
    NOT = 354,
    B_NOT = 355,
    SIZEOF = 356,
    ALIGNOF = 357,
    INCR = 358,
    DECR = 359,
    HYPERUNARY = 360,
    ARROW = 361,
    DOT = 362,
    LPAREN = 363,
    LBRCKT = 364
  };
#endif

/* Value type.  */



int yyparse (void);

#endif /* !YY_YY_C_GRAM_H_INCLUDED  */
