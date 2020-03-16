/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 3 "c_gram.y" /* yacc.c:339  */

 /*
 ======================================================================
 CTREE Version 0.09
 Written by Shaun Flisakowski (1995)
 With small revisions for use in UNO
 by Gerard Holzmann, Bell Labs (2000-2001)
 by Russ Cox, Bell Labs (2003)
 by Brian Kernighan, Princeton (2005)
 ======================================================================
  This program is provided free of charge on an "as is" basis without
  warranty of any kind, either express or implied.  Acceptance and use
  of this program constitutes the user's understanding that (s)he will
  have no recourse for any actual or consequential damages, including,
  but not limited to, lost profits or savings, arising out of the use
  of or inability to use this program.  
 ======================================================================
  this grammar is based on "C - A Reference Manual" (4th Ed.),
  by Samuel P Harbison, and Guy L Steele Jr.
 */

#define	alloca	emalloc
#define	YYERROR_VERBOSE

#include <ctype.h>
#include "globals.h"
#include "lexer.h"
#include "tree.h"
#include "symtab.h"

#define YYDEBUG 1

static int debug = 0;
extern int see_static_fcts;
extern int see_extern_fcts;
extern int list_typedefs;
#if 0
int  yydebug = 1;
#endif

int structfieldflag;

extern int errno, err_cnt, Verbose;
extern char *progname;
extern int yylex(YYSTYPE *lvalp);
extern void name_scope(context_t *, char *, int);
extern char *toksym(int, int);

extern TreeStack *ParseStack;	/* uno_local.c */
extern Stk_Item  *Parse_TOS;	/* uno_local.c */

static void insert_decl     (leafnode *, treenode *, treenode *);
static void insert_typedef  (leafnode *, treenode *, treenode *);
static void insert_component(leafnode *, treenode *, treenode *);
extern void add_constant(char *);
static void add_params_to_symtab(treenode *);
extern void *emalloc(size_t);
extern void location(treenode *);
extern int has_upper(char *s);
extern int exclude_location(treenode *);
			

#line 129 "c_gram.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "c_gram.h".  */
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

/* Copy the second part of user declarations.  */

#line 284 "c_gram.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  69
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1449

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  110
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  145
/* YYNRULES -- Number of rules.  */
#define YYNRULES  294
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  436

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   364

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   188,   188,   193,   199,   207,   208,   219,   222,   225,
     232,   238,   276,   286,   300,   303,   306,   307,   323,   326,
     329,   330,   339,   340,   344,   343,   355,   362,   368,   374,
     380,   386,   392,   398,   404,   410,   416,   422,   428,   435,
     441,   450,   451,   454,   455,   456,   459,   469,   476,   483,
     491,   517,   524,   535,   548,   560,   570,   583,   599,   600,
     601,   604,   605,   618,   619,   628,   629,   638,   645,   646,
     655,   656,   665,   666,   675,   682,   683,   690,   701,   702,
     711,   712,   721,   722,   731,   732,   741,   742,   751,   752,
     753,   754,   755,   756,   757,   758,   759,   760,   761,   764,
     771,   778,   785,   792,   799,   807,   814,   821,   828,   835,
     836,   846,   849,   852,   856,   859,   862,   865,   866,   875,
     879,   880,   886,   892,   900,   901,   902,   903,   904,   905,
     908,   918,   919,   922,   930,   939,   942,   945,   946,   959,
     978,   986,   989,   990,   993,   994,   995,   998,  1001,  1004,
    1005,  1008,  1031,  1038,  1041,  1048,  1051,  1054,  1061,  1068,
    1077,  1084,  1094,  1097,  1100,  1101,  1111,  1114,  1117,  1118,
    1127,  1128,  1137,  1138,  1141,  1142,  1150,  1153,  1156,  1164,
    1167,  1170,  1171,  1181,  1184,  1187,  1188,  1189,  1190,  1191,
    1194,  1195,  1196,  1197,  1198,  1199,  1200,  1201,  1202,  1203,
    1204,  1205,  1206,  1209,  1210,  1213,  1214,  1217,  1223,  1224,
    1228,  1231,  1234,  1238,  1241,  1269,  1276,  1277,  1286,  1287,
    1296,  1311,  1314,  1318,  1317,  1356,  1364,  1363,  1405,  1412,
    1413,  1422,  1431,  1432,  1439,  1446,  1447,  1450,  1453,  1466,
    1469,  1470,  1473,  1479,  1489,  1492,  1495,  1502,  1505,  1512,
    1518,  1519,  1527,  1535,  1544,  1553,  1561,  1562,  1570,  1573,
    1576,  1577,  1586,  1587,  1596,  1603,  1610,  1618,  1622,  1631,
    1634,  1635,  1638,  1649,  1650,  1656,  1665,  1671,  1677,  1685,
    1691,  1701,  1712,  1711,  1725,  1724,  1737,  1747,  1748,  1751,
    1752,  1765,  1766,  1767,  1768
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "IDENT", "STRING", "FIELD_NAME",
  "TYPEDEF_NAME", "TAG", "CHAR_CONST", "INUM", "RNUM", "COMMENT",
  "PP_DEFINE", "INVALID", "AUTO", "BREAK", "CASE", "CHAR", "CONST", "CONT",
  "DEFLT", "DO", "DOUBLE", "ELSE", "ENUM", "EXTRN", "IF", "FOR", "FLOAT",
  "GOTO", "INT", "LONG", "REGISTR", "RETURN", "SHORT", "SGNED", "STATIC",
  "STRUCT", "SWITCH", "TYPEDEF", "UNION", "UNSGNED", "VOID", "VOLATILE",
  "WHILE", "PLUS_EQ", "MINUS_EQ", "STAR_EQ", "DIV_EQ", "MOD_EQ",
  "B_NOT_EQ", "B_AND_EQ", "B_OR_EQ", "B_XOR_EQ", "L_SHIFT_EQ",
  "R_SHIFT_EQ", "EQUAL", "LESS_EQ", "GRTR_EQ", "NOT_EQ", "RPAREN",
  "RBRCKT", "LBRACE", "RBRACE", "SEMICOLON", "COMMA", "ELLIPSIS",
  "LB_SIGN", "DOUB_LB_SIGN", "BACKQUOTE", "AT", "DOLLAR", "CPP_INCLUDE",
  "CPP_DEFINE", "CPP_LINE", "COMMA_OP", "EQ", "ASSIGN", "QUESTMARK",
  "COLON", "COMMA_SEP", "OR", "AND", "B_OR", "B_XOR", "B_AND", "COMP_EQ",
  "COMP_ARITH", "LESS", "GRTR", "L_SHIFT", "R_SHIFT", "PLUS", "MINUS",
  "STAR", "DIV", "MOD", "CAST", "UNARY", "NOT", "B_NOT", "SIZEOF",
  "ALIGNOF", "INCR", "DECR", "HYPERUNARY", "ARROW", "DOT", "LPAREN",
  "LBRCKT", "$accept", "program", "trans_unit", "top_level_decl",
  "func_def", "func_spec", "opt_decl_list", "decl_list",
  "opt_block_item_list", "block_item_list", "block_item", "cmpnd_stemnt",
  "$@1", "stemnt", "expr_stemnt", "labeled_stemnt", "cond_stemnt",
  "iter_stemnt", "switch_stemnt", "break_stemnt", "continue_stemnt",
  "return_stemnt", "goto_stemnt", "null_stemnt", "if_stemnt",
  "if_else_stemnt", "do_stemnt", "while_stemnt", "for_stemnt", "label",
  "cond_expr", "log_or_expr", "log_and_expr", "log_neg_expr",
  "bitwise_or_expr", "bitwise_xor_expr", "bitwise_and_expr",
  "bitwise_neg_expr", "cast_expr", "equality_expr", "relational_expr",
  "shift_expr", "additive_expr", "mult_expr", "unary_expr", "sizeof_expr",
  "alignof_expr", "unary_minus_expr", "unary_plus_expr", "addr_expr",
  "indirection_expr", "preinc_expr", "predec_expr", "assign_expr",
  "opt_const_expr", "const_expr", "opt_expr", "expr", "comma_expr",
  "prim_expr", "paren_expr", "postfix_expr", "subscript_expr",
  "comp_select_expr", "postinc_expr", "postdec_expr", "opt_expr_list",
  "expr_list", "named_label", "case_label", "deflt_label", "add_op",
  "mult_op", "equality_op", "relation_op", "shift_op", "declaration",
  "opt_comment", "opt_decl_specs", "decl_specs", "comp_decl_specs",
  "opt_comp_decl_specs", "init_decl", "opt_init_decl_list",
  "init_decl_list", "initializer_list", "opt_eq", "initializer",
  "opt_comma", "type_qual_list", "opt_type_qual_list", "storage_class",
  "type_spec", "enum_type_spec", "struct_type_spec", "typedef_name",
  "union_type_spec", "opt_tag", "tag", "enum_type_define", "enum_type_ref",
  "enum_def_list", "enum_const_def", "enum_constant", "opt_trailing_comma",
  "struct_type_define", "$@2", "struct_type_ref", "union_type_define",
  "$@3", "union_type_ref", "field_list", "comp_decl", "comp_decl_list",
  "comp_declarator", "simple_comp", "bit_field", "width", "type_qual",
  "type_name", "opt_declarator", "declarator", "direct_declarator",
  "simple_decl", "pointer_start", "pointer", "opt_param_type_list",
  "param_type_list", "param_list", "param_decl", "ident_list", "ident",
  "field_ident", "typename_as_ident", "abs_decl", "direct_abs_decl",
  "array_decl", "direct_comp_select", "$@4", "indirect_comp_select", "$@5",
  "func_call", "assign_op", "strings", "constant", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,   362,   363,   364
};
# endif

#define YYPACT_NINF -274

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-274)))

#define YYTABLE_NINF -273

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     327,   -32,  -274,  -274,  -274,  -274,  -274,  -274,  -274,    50,
    -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,    50,  -274,
      50,  -274,  -274,  -274,  -274,    11,    78,    41,   375,  -274,
    -274,    16,  -274,    78,  1379,  1379,  -274,  -274,    24,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,  1379,  1347,   -50,  -274,
     -31,    40,  -274,  -274,  -274,  -274,  -274,  -274,    17,    37,
    -274,    44,    37,    63,    37,    11,  -274,  -274,    23,  -274,
     -32,  -274,    69,  -274,  -274,  -274,    25,    80,  1169,  -274,
    -274,  -274,  -274,  -274,  -274,  1347,  -274,    78,  1250,   920,
    -274,   -50,   139,  -274,  -274,  -274,  -274,  -274,   470,  -274,
      78,   860,  -274,  -274,    76,  -274,  -274,    49,    96,    94,
    -274,   -46,  -274,  -274,  -274,  -274,  -274,   920,   920,   920,
     920,   920,   920,   933,  1035,  1069,  1069,   682,  -274,    -7,
      89,  -274,    84,    93,    88,  -274,  -274,   101,   104,    33,
      77,     1,    99,  -274,  -274,  -274,  -274,  -274,  -274,  -274,
    -274,  -274,   138,  -274,  -274,   136,  -274,  -274,    57,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,  -274,   198,  -274,  -274,
     140,  -274,   127,  1406,  1406,   121,   125,   142,   920,   143,
    -274,   725,   102,   103,   209,   920,   108,   110,  -274,   156,
     576,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,   141,
     158,  -274,  -274,  -274,  -274,  -274,   799,    70,   920,  -274,
    -274,   817,   920,  -274,    21,  -274,    81,  -274,  1207,  -274,
     209,  -274,  -274,  -274,  -274,  -274,  -274,  -274,   682,  -274,
     682,  -274,   437,  -274,  -274,   163,   166,   -60,   167,   920,
     920,   920,   920,   920,   920,  -274,   920,  -274,   920,  -274,
    -274,   920,  -274,  -274,   920,  -274,  -274,  -274,   920,  -274,
    -274,   920,  -274,   920,  -274,  -274,  -274,  -274,   920,   920,
    -274,   139,   165,   920,    74,  1406,  1277,  -274,  1406,  1307,
    -274,  -274,  -274,  -274,   185,   920,   967,   169,   171,  -274,
     920,   920,  -274,  -274,   725,   220,  -274,   174,  -274,   160,
     179,   181,  -274,   183,   184,    81,  1379,   920,  -274,  -274,
    -274,   191,   193,  -274,  -274,  1070,    86,  -274,   457,   177,
      89,    84,    93,    88,   101,   104,    33,    77,     1,  -274,
    -274,  -274,    70,    70,  -274,   202,   200,   197,  -274,  -274,
    -274,  -274,   133,  -274,  -274,  -274,   187,   190,  -274,  -274,
    -274,  -274,  -274,  -274,   155,   210,   207,   920,  -274,  -274,
     212,   213,  -274,  -274,  -274,   860,   211,  -274,   860,   160,
    -274,  -274,  -274,   216,   218,  -274,  -274,   860,  -274,   920,
    -274,  -274,  -274,   920,  -274,  -274,    78,   920,   920,   725,
     920,   217,   725,   725,  -274,  -274,  -274,   860,  -274,  -274,
      39,  -274,  -274,  -274,  -274,  -274,   222,   254,   219,   920,
    -274,  -274,  -274,  -274,   860,   223,   725,   920,   232,  -274,
    -274,   235,   725,   725,  -274,  -274
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
       0,     4,   254,   207,   152,   185,   195,   240,   200,   210,
     186,   199,   197,   198,   187,   196,   201,   188,   210,   189,
     210,   202,   194,   241,     9,   183,     0,     0,     0,     5,
       8,     0,     7,   166,   155,   155,   190,   191,   192,   193,
     203,   204,   205,   206,   208,   209,   155,    14,   247,   270,
     256,     0,   248,   271,   250,    10,   212,   272,     0,   215,
     213,     0,   225,     0,   228,   184,   255,   181,     0,     1,
       0,     6,     0,    24,    11,   168,     0,   167,    14,   157,
     156,   192,   158,   159,    13,    15,    16,   166,     0,   111,
     257,   246,     0,   223,   226,   182,   249,    26,     0,   151,
       0,     0,    12,    17,   164,   269,   253,   266,     0,   260,
     262,     0,   267,   289,   293,   291,   292,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   109,    61,
      63,    93,    65,    68,    70,    94,    86,    72,    78,    80,
      82,    84,    75,    89,    90,    91,    92,    95,    96,    97,
      98,   117,     0,   112,   113,   116,   124,   120,    88,   125,
     126,   128,   129,   119,   131,   132,   127,   294,   121,   220,
     221,   216,   218,     0,     0,     0,   269,     0,     0,     0,
     141,     0,     0,     0,     0,   114,     0,     0,    51,     0,
       0,    20,    29,    23,    27,    28,    30,    31,    32,    33,
      34,    35,    36,    37,    41,    42,    43,    44,    45,     0,
       0,    58,    59,    60,    22,   169,     0,     0,     0,   174,
     165,   258,   111,   264,   273,   265,   274,   251,     0,   252,
       0,   105,    75,   104,   103,   106,    67,    74,     0,   100,
       0,   102,     0,   107,   108,     0,     0,   242,     0,     0,
       0,     0,     0,     0,     0,   147,     0,   148,     0,   149,
     150,     0,   142,   143,     0,   144,   145,   146,     0,   287,
     288,     0,   281,     0,   133,   134,   284,   282,   135,     0,
     290,   222,     0,     0,   244,   162,     0,   229,   162,     0,
      38,    47,   140,    48,     0,     0,   114,     0,     0,   115,
       0,     0,    25,    21,     0,   153,   178,   179,   170,   172,
       0,     0,   259,     0,     0,   275,   258,   111,   261,   263,
     268,     0,     0,   123,   122,   258,   273,   243,     0,     0,
      64,    66,    69,    71,    73,    79,    81,    83,    85,    87,
     110,   118,     0,     0,   137,     0,   136,     0,   217,   214,
     219,   234,     0,   232,   235,   236,     0,   237,   163,   160,
     224,   230,   161,   227,     0,     0,     0,   114,    50,    49,
       0,     0,    40,   154,    39,   180,     0,   173,     0,   172,
     279,   276,   277,     0,     0,    99,   101,     0,    76,     0,
     285,   283,   286,     0,   130,   231,   244,     0,     0,     0,
     114,     0,     0,     0,   171,   175,   177,     0,   280,   278,
       0,    62,   138,   233,   239,   238,     0,    52,     0,   114,
      46,    55,   176,    77,     0,     0,     0,   114,     0,    54,
      53,     0,     0,     0,    57,    56
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -274,  -274,  -274,   268,  -274,  -274,   221,  -274,  -274,  -274,
     111,   267,  -274,  -165,  -274,  -274,  -274,  -274,  -274,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,
     -85,  -274,    52,  -274,    54,    48,    53,  -274,   -53,    55,
      56,    58,    47,    46,    -4,  -274,  -274,  -274,  -274,  -274,
    -274,  -274,  -274,   -90,  -209,   137,  -273,   -87,  -274,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,  -274,
    -274,  -274,  -274,  -274,  -274,  -274,   -41,  -274,    26,     4,
    -200,    31,   214,  -274,  -274,   -66,   -57,   -89,  -274,  -274,
    -274,  -274,  -152,  -274,  -274,     0,  -274,    85,    91,  -274,
    -274,  -274,    42,  -274,  -274,  -274,  -274,  -274,  -274,  -274,
    -274,   151,  -196,  -274,   -70,  -274,  -274,  -274,     5,  -128,
    -274,   -25,   -44,  -274,  -274,   -47,    15,   248,  -274,   109,
    -274,   -83,  -202,    27,   -97,  -182,  -274,  -274,  -274,  -274,
    -274,  -274,  -274,  -274,  -274
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    27,    28,    29,    30,    31,    84,    85,   189,   190,
     191,   192,    98,   193,   194,   195,   196,   197,   198,   199,
     200,   201,   202,   203,   204,   205,   206,   207,   208,   209,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,   139,   140,   141,   142,   143,   144,   145,   146,   147,
     148,   149,   150,   151,   152,   153,   298,   210,   155,   156,
     157,   158,   159,   160,   161,   162,   345,   346,   211,   212,
     213,   264,   268,   256,   258,   261,    32,   374,    79,    87,
     284,   359,    75,    76,    77,   307,   378,   308,   376,    65,
      66,    34,    35,    36,    37,    81,    39,    58,    59,    40,
      41,   170,   171,   172,   282,    42,   173,    43,    44,   174,
      45,   286,   287,   352,   353,   354,   355,   415,    46,   248,
     356,    47,    48,    49,    50,    51,   311,   312,   109,   110,
     111,   163,    52,    53,   313,   226,    54,   164,   343,   165,
     342,   166,   271,   167,   168
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      38,    68,   154,    90,    33,   112,    86,    91,    78,    57,
     225,   219,   220,   314,   229,   309,   294,    72,    57,   230,
      57,   285,   285,   366,     2,  -272,    57,     3,    38,     7,
      67,    55,    33,    57,    25,  -272,    60,    86,    80,    80,
     246,    69,   315,     2,   103,    60,     3,    60,   325,   222,
      80,    57,     2,    56,    23,     3,     3,   214,    88,    89,
     224,    82,   104,    25,   231,   233,   234,   235,   236,   237,
      95,   249,    83,     2,   250,   104,     3,     2,    73,    92,
       3,     2,   223,    96,     3,   358,  -272,    57,   358,    99,
     361,   154,   107,   361,   401,   265,   266,   267,   299,  -211,
      57,   297,   423,    61,   424,    63,    93,    57,   384,    62,
     321,    64,   322,   232,   232,   232,   232,   232,   232,   239,
     241,   243,   244,   259,   260,    94,   219,   418,   310,   221,
     222,   247,    97,   285,   285,   154,   285,   285,   351,   372,
     390,   391,   169,    25,   315,   100,   428,   320,    26,   214,
     327,   246,   101,   246,   431,   246,   227,   221,   222,   228,
     274,   275,   329,   276,   277,   278,   279,   252,    25,   262,
     263,   251,    25,   254,   224,   269,   270,   253,   288,   288,
      91,   340,    26,   341,    97,   290,    26,   255,   344,   316,
     317,   257,   347,   350,   325,   222,    68,   395,   396,   272,
     326,   273,   280,   283,  -139,   281,   291,   293,   365,   299,
     295,   296,   105,   370,   371,   339,   300,    57,   301,   302,
     304,    38,   305,   323,    57,   107,   324,   328,   349,   364,
     154,   373,   107,   368,   417,   369,   377,   420,   421,   375,
     379,   380,   247,   381,   247,   382,   232,   232,   232,   232,
     232,   385,   232,   386,   232,   367,   389,   232,   394,   357,
     232,   430,   392,   398,   232,   393,   397,   434,   435,  -245,
     399,   400,   402,   403,   405,   388,   408,   426,   326,   409,
     299,   419,   425,   427,    57,   219,   404,   429,   219,   406,
     288,   288,   432,   288,   288,   433,    71,   219,    74,   102,
     332,   303,   330,   412,   411,   331,   333,   414,   337,   334,
     338,   416,   335,   299,   215,   292,   336,   219,   422,   362,
     107,   410,   407,   348,   232,   289,   413,    -2,     1,   107,
       2,   383,   299,     3,   219,   404,   108,   319,     4,     0,
     299,     5,    57,    57,     6,     7,     0,     0,     0,     8,
       0,     9,    10,     0,     0,    11,     0,    12,    13,    14,
       0,    15,    16,    17,    18,     0,    19,    20,    21,    22,
      23,   357,     0,     0,     0,    -3,    70,     0,     2,     0,
       0,     3,     0,     0,     0,   232,     4,     0,     0,     5,
       0,    24,     6,     7,     0,     0,    57,     8,     0,     9,
      10,     0,     0,    11,     0,    12,    13,    14,     0,    15,
      16,    17,    18,     0,    19,    20,    21,    22,    23,     0,
       0,    25,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    26,     0,     0,   245,    24,
     105,   113,     0,     0,     0,   114,   115,   116,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     105,   113,     0,     0,     0,   114,   115,   116,     0,    25,
       0,   175,     0,   176,   113,     0,     3,     0,   114,   115,
     116,     4,     0,    26,     5,   177,   178,     6,     7,   179,
     180,   181,     8,     0,     9,    10,   182,   183,    11,   184,
      12,    13,    14,   185,    15,    16,    17,    18,   186,    19,
      20,    21,    22,    23,   187,     0,     0,     0,     0,   387,
       0,     0,   117,     0,     0,     0,     0,     0,     0,   118,
     119,   120,    73,   -18,   188,     0,   121,   122,   123,   124,
     125,   126,   117,     0,     0,   127,     0,     0,     0,   118,
     119,   120,     0,     0,     0,   117,   121,   122,   123,   124,
     125,   126,   118,   119,   120,   127,     0,     0,     0,   121,
     122,   123,   124,   125,   126,     0,     0,   175,   127,   176,
     113,     0,     3,     0,   114,   115,   116,     4,     0,     0,
       5,   177,   178,     6,     7,   179,   180,   181,     8,     0,
       9,    10,   182,   183,    11,   184,    12,    13,    14,   185,
      15,    16,    17,    18,   186,    19,    20,    21,    22,    23,
     187,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    73,   -19,
     188,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   117,     0,     0,     0,     0,     0,     0,   118,   119,
     120,     0,     0,     0,     0,   121,   122,   123,   124,   125,
     126,     0,     0,   245,   127,   105,   113,     0,     3,     0,
     114,   115,   116,     0,     0,     0,     5,     0,     0,     6,
       7,     0,     0,     0,     8,     0,     9,    10,     0,     0,
      11,     0,    12,    13,    14,     0,    15,    16,    17,    18,
       0,    19,    20,    21,    22,    23,   175,     0,   176,   113,
       0,     0,     0,   114,   115,   116,     0,     0,     0,     0,
     177,   178,     0,     0,   179,   180,   181,     0,     0,     0,
       0,   182,   183,     0,   184,     0,     0,     0,   185,     0,
       0,     0,     0,   186,     0,     0,     0,   117,     0,   187,
       0,     0,     0,     0,   118,   119,   120,     0,     0,     0,
       0,   121,   122,   123,   124,   125,   126,    73,     0,   188,
     127,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   105,   113,     0,     0,     0,   114,   115,   116,
     117,     0,     0,     0,     0,     0,     0,   118,   119,   120,
       2,     0,     0,     3,   121,   122,   123,   124,   125,   126,
       0,     5,     0,   127,     6,     7,     0,     0,     0,     8,
       0,     9,    10,     0,     0,    11,     0,    12,    13,    14,
       0,    15,    16,    17,    18,     0,    19,    20,    21,    22,
      23,   216,   306,   105,   113,     0,     0,     0,   114,   115,
     116,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   117,     0,     0,     0,     0,     0,
       0,   118,   119,   120,     0,     0,     0,     0,   121,   122,
     123,   124,   125,   126,     0,     0,   217,   127,   218,     0,
       0,    25,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   216,   105,   113,   221,   222,     0,   114,   115,
     116,     0,     0,     0,     0,     0,   105,   113,     0,     0,
       0,   114,   115,   116,     0,   117,     0,     0,     0,     0,
       0,     0,   118,   119,   120,     0,     0,     0,     0,   121,
     122,   123,   124,   125,   126,     0,     0,   217,   127,   218,
     105,   113,     0,     3,     0,   114,   115,   116,     4,     0,
       0,     5,     0,     0,     6,     7,     0,     0,     0,     8,
       0,     9,    10,     0,     0,    11,     0,    12,    13,    14,
       0,    15,    16,    17,    18,   117,    19,    20,    21,    22,
      23,     0,   118,   119,   120,     0,     0,     0,   117,   121,
     122,   123,   124,   125,   126,   118,   119,   120,   127,     0,
       0,     0,   121,   122,   123,   124,   125,   126,   105,   113,
       0,   238,     0,   114,   115,   116,     0,     0,     0,     0,
       0,     0,   117,     0,     0,     0,     0,     0,     0,   118,
     119,   120,     0,     0,     0,     0,   121,   122,   123,   124,
     125,   126,   105,   113,     0,   127,     3,   114,   115,   116,
       0,     0,     0,     0,     5,     0,     0,     6,     7,     0,
       0,     0,     8,     0,     9,    10,     0,     0,    11,     0,
      12,    13,    14,     0,    15,    16,    17,    18,     0,    19,
      20,    21,    22,    23,     0,     0,     0,     0,     0,     0,
     117,     0,     0,     0,     0,     0,     0,   118,   119,   120,
       0,     0,     0,     0,   121,   122,   123,   124,   125,   126,
       0,     0,     0,   240,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   117,     0,     0,     0,     0,     0,
       0,   118,   119,   120,    25,     0,     0,     0,   121,   122,
     123,   124,   125,   126,     0,     3,     0,   242,   325,   222,
       4,     0,     0,     5,     0,     0,     6,     7,     0,     0,
       0,     8,     0,     9,    10,     0,     0,    11,     0,    12,
      13,    14,     0,    15,    16,    17,    18,     0,    19,    20,
      21,    22,    23,     3,     0,     0,     0,     0,     0,     0,
       0,     5,     0,     0,     6,     7,     0,     0,     0,     8,
       0,     9,    10,  -164,  -164,    11,     0,    12,    13,    14,
       0,    15,    16,    17,    18,   101,    19,    20,    21,    22,
      23,     0,     0,   105,     0,     0,     3,     0,     0,     0,
       0,     0,     0,     0,     5,     0,     0,     6,     7,     0,
       0,     0,     8,   318,     9,    10,     0,     0,    11,     0,
      12,    13,    14,     3,    15,    16,    17,    18,     0,    19,
      20,    21,    22,    23,     6,     7,     0,     0,     0,     8,
       0,     9,     0,     0,     0,    11,     0,    12,    13,     0,
     106,    15,    16,     3,    18,     0,     0,    20,    21,    22,
      23,     0,     0,     0,     6,     7,     0,     0,     0,     8,
       0,     9,     0,     0,     0,    11,     0,    12,    13,     0,
     360,    15,    16,     0,    18,     0,     0,    20,    21,    22,
      23,     0,     0,     3,     0,     0,     0,     0,     4,     0,
       0,     5,     0,     0,     6,     7,     0,     0,     0,     8,
     363,     9,    10,     0,     0,    11,     0,    12,    13,    14,
       0,    15,    16,    17,    18,     3,    19,    20,    21,    22,
      23,     0,     0,     5,     0,     0,     6,     7,     0,     0,
       0,     8,     0,     9,    10,     0,     0,    11,     0,    12,
      13,    14,     3,    15,    16,    17,    18,     0,    19,    20,
      21,    22,    23,     6,     7,     0,     0,     0,     8,     0,
       9,     0,     0,     0,    11,     0,    12,    13,     0,     0,
      15,    16,     0,    18,     0,     0,    20,    21,    22,    23
};

static const yytype_int16 yycheck[] =
{
       0,    26,    89,    50,     0,    88,    47,    51,    33,     9,
     107,   101,   101,   222,    60,   217,   181,     1,    18,    65,
      20,   173,   174,   296,     3,     1,    26,     6,    28,    18,
      25,    63,    28,    33,    94,    11,     9,    78,    34,    35,
     127,     0,   224,     3,    85,    18,     6,    20,   108,   109,
      46,    51,     3,     3,    43,     6,     6,    98,   108,   109,
     107,    35,    87,    94,   117,   118,   119,   120,   121,   122,
      65,    78,    46,     3,    81,   100,     6,     3,    62,    62,
       6,     3,   107,    60,     6,   285,    62,    87,   288,    64,
     286,   178,    88,   289,   367,    94,    95,    96,   185,    62,
     100,   184,    63,    18,    65,    20,    62,   107,   317,    18,
     238,    20,   240,   117,   118,   119,   120,   121,   122,   123,
     124,   125,   126,    90,    91,    62,   216,   400,   218,   108,
     109,   127,    63,   285,   286,   222,   288,   289,    64,   304,
     342,   343,     3,    94,   326,    65,   419,   230,   108,   190,
     247,   238,    76,   240,   427,   242,    60,   108,   109,    65,
     103,   104,   249,   106,   107,   108,   109,    83,    94,    92,
      93,    82,    94,    85,   221,    76,    77,    84,   173,   174,
     224,   271,   108,   273,    63,    64,   108,    86,   278,   108,
     109,    87,   279,   283,   108,   109,   221,    64,    65,    61,
     247,    65,     4,    76,    79,    65,    64,    64,   295,   296,
     108,   108,     3,   300,   301,   268,   108,   217,   108,    63,
      79,   221,    64,    60,   224,   221,    60,    60,    63,    44,
     317,    11,   228,    64,   399,    64,    76,   402,   403,    65,
      61,    60,   238,    60,   240,    61,   250,   251,   252,   253,
     254,    60,   256,    60,   258,   296,    79,   261,    61,   284,
     264,   426,    60,   108,   268,    65,    79,   432,   433,    79,
      60,    64,    60,    60,    63,   328,    60,    23,   325,    61,
     367,    64,    60,    64,   284,   375,   375,    64,   378,   378,
     285,   286,    60,   288,   289,    60,    28,   387,    31,    78,
     252,   190,   250,   393,   389,   251,   253,   397,   261,   254,
     264,   398,   256,   400,   100,   178,   258,   407,   407,   288,
     316,   387,   379,   281,   328,   174,   396,     0,     1,   325,
       3,   316,   419,     6,   424,   424,    88,   228,    11,    -1,
     427,    14,   342,   343,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    25,    -1,    -1,    28,    -1,    30,    31,    32,
      -1,    34,    35,    36,    37,    -1,    39,    40,    41,    42,
      43,   396,    -1,    -1,    -1,     0,     1,    -1,     3,    -1,
      -1,     6,    -1,    -1,    -1,   389,    11,    -1,    -1,    14,
      -1,    64,    17,    18,    -1,    -1,   396,    22,    -1,    24,
      25,    -1,    -1,    28,    -1,    30,    31,    32,    -1,    34,
      35,    36,    37,    -1,    39,    40,    41,    42,    43,    -1,
      -1,    94,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   108,    -1,    -1,     1,    64,
       3,     4,    -1,    -1,    -1,     8,     9,    10,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
       3,     4,    -1,    -1,    -1,     8,     9,    10,    -1,    94,
      -1,     1,    -1,     3,     4,    -1,     6,    -1,     8,     9,
      10,    11,    -1,   108,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    -1,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    -1,    -1,    -1,    -1,    62,
      -1,    -1,    85,    -1,    -1,    -1,    -1,    -1,    -1,    92,
      93,    94,    62,    63,    64,    -1,    99,   100,   101,   102,
     103,   104,    85,    -1,    -1,   108,    -1,    -1,    -1,    92,
      93,    94,    -1,    -1,    -1,    85,    99,   100,   101,   102,
     103,   104,    92,    93,    94,   108,    -1,    -1,    -1,    99,
     100,   101,   102,   103,   104,    -1,    -1,     1,   108,     3,
       4,    -1,     6,    -1,     8,     9,    10,    11,    -1,    -1,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    -1,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    62,    63,
      64,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    85,    -1,    -1,    -1,    -1,    -1,    -1,    92,    93,
      94,    -1,    -1,    -1,    -1,    99,   100,   101,   102,   103,
     104,    -1,    -1,     1,   108,     3,     4,    -1,     6,    -1,
       8,     9,    10,    -1,    -1,    -1,    14,    -1,    -1,    17,
      18,    -1,    -1,    -1,    22,    -1,    24,    25,    -1,    -1,
      28,    -1,    30,    31,    32,    -1,    34,    35,    36,    37,
      -1,    39,    40,    41,    42,    43,     1,    -1,     3,     4,
      -1,    -1,    -1,     8,     9,    10,    -1,    -1,    -1,    -1,
      15,    16,    -1,    -1,    19,    20,    21,    -1,    -1,    -1,
      -1,    26,    27,    -1,    29,    -1,    -1,    -1,    33,    -1,
      -1,    -1,    -1,    38,    -1,    -1,    -1,    85,    -1,    44,
      -1,    -1,    -1,    -1,    92,    93,    94,    -1,    -1,    -1,
      -1,    99,   100,   101,   102,   103,   104,    62,    -1,    64,
     108,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     3,     4,    -1,    -1,    -1,     8,     9,    10,
      85,    -1,    -1,    -1,    -1,    -1,    -1,    92,    93,    94,
       3,    -1,    -1,     6,    99,   100,   101,   102,   103,   104,
      -1,    14,    -1,   108,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    25,    -1,    -1,    28,    -1,    30,    31,    32,
      -1,    34,    35,    36,    37,    -1,    39,    40,    41,    42,
      43,    62,    63,     3,     4,    -1,    -1,    -1,     8,     9,
      10,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    85,    -1,    -1,    -1,    -1,    -1,
      -1,    92,    93,    94,    -1,    -1,    -1,    -1,    99,   100,
     101,   102,   103,   104,    -1,    -1,   107,   108,   109,    -1,
      -1,    94,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    62,     3,     4,   108,   109,    -1,     8,     9,
      10,    -1,    -1,    -1,    -1,    -1,     3,     4,    -1,    -1,
      -1,     8,     9,    10,    -1,    85,    -1,    -1,    -1,    -1,
      -1,    -1,    92,    93,    94,    -1,    -1,    -1,    -1,    99,
     100,   101,   102,   103,   104,    -1,    -1,   107,   108,   109,
       3,     4,    -1,     6,    -1,     8,     9,    10,    11,    -1,
      -1,    14,    -1,    -1,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    25,    -1,    -1,    28,    -1,    30,    31,    32,
      -1,    34,    35,    36,    37,    85,    39,    40,    41,    42,
      43,    -1,    92,    93,    94,    -1,    -1,    -1,    85,    99,
     100,   101,   102,   103,   104,    92,    93,    94,   108,    -1,
      -1,    -1,    99,   100,   101,   102,   103,   104,     3,     4,
      -1,   108,    -1,     8,     9,    10,    -1,    -1,    -1,    -1,
      -1,    -1,    85,    -1,    -1,    -1,    -1,    -1,    -1,    92,
      93,    94,    -1,    -1,    -1,    -1,    99,   100,   101,   102,
     103,   104,     3,     4,    -1,   108,     6,     8,     9,    10,
      -1,    -1,    -1,    -1,    14,    -1,    -1,    17,    18,    -1,
      -1,    -1,    22,    -1,    24,    25,    -1,    -1,    28,    -1,
      30,    31,    32,    -1,    34,    35,    36,    37,    -1,    39,
      40,    41,    42,    43,    -1,    -1,    -1,    -1,    -1,    -1,
      85,    -1,    -1,    -1,    -1,    -1,    -1,    92,    93,    94,
      -1,    -1,    -1,    -1,    99,   100,   101,   102,   103,   104,
      -1,    -1,    -1,   108,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    85,    -1,    -1,    -1,    -1,    -1,
      -1,    92,    93,    94,    94,    -1,    -1,    -1,    99,   100,
     101,   102,   103,   104,    -1,     6,    -1,   108,   108,   109,
      11,    -1,    -1,    14,    -1,    -1,    17,    18,    -1,    -1,
      -1,    22,    -1,    24,    25,    -1,    -1,    28,    -1,    30,
      31,    32,    -1,    34,    35,    36,    37,    -1,    39,    40,
      41,    42,    43,     6,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    14,    -1,    -1,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    25,    64,    65,    28,    -1,    30,    31,    32,
      -1,    34,    35,    36,    37,    76,    39,    40,    41,    42,
      43,    -1,    -1,     3,    -1,    -1,     6,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    14,    -1,    -1,    17,    18,    -1,
      -1,    -1,    22,    66,    24,    25,    -1,    -1,    28,    -1,
      30,    31,    32,     6,    34,    35,    36,    37,    -1,    39,
      40,    41,    42,    43,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,
      60,    34,    35,     6,    37,    -1,    -1,    40,    41,    42,
      43,    -1,    -1,    -1,    17,    18,    -1,    -1,    -1,    22,
      -1,    24,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,
      63,    34,    35,    -1,    37,    -1,    -1,    40,    41,    42,
      43,    -1,    -1,     6,    -1,    -1,    -1,    -1,    11,    -1,
      -1,    14,    -1,    -1,    17,    18,    -1,    -1,    -1,    22,
      63,    24,    25,    -1,    -1,    28,    -1,    30,    31,    32,
      -1,    34,    35,    36,    37,     6,    39,    40,    41,    42,
      43,    -1,    -1,    14,    -1,    -1,    17,    18,    -1,    -1,
      -1,    22,    -1,    24,    25,    -1,    -1,    28,    -1,    30,
      31,    32,     6,    34,    35,    36,    37,    -1,    39,    40,
      41,    42,    43,    17,    18,    -1,    -1,    -1,    22,    -1,
      24,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,    -1,
      34,    35,    -1,    37,    -1,    -1,    40,    41,    42,    43
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     1,     3,     6,    11,    14,    17,    18,    22,    24,
      25,    28,    30,    31,    32,    34,    35,    36,    37,    39,
      40,    41,    42,    43,    64,    94,   108,   111,   112,   113,
     114,   115,   186,   189,   201,   202,   203,   204,   205,   206,
     209,   210,   215,   217,   218,   220,   228,   231,   232,   233,
     234,   235,   242,   243,   246,    63,     3,   205,   207,   208,
     243,   207,   208,   207,   208,   199,   200,   228,   231,     0,
       1,   113,     1,    62,   121,   192,   193,   194,   231,   188,
     189,   205,   188,   188,   116,   117,   186,   189,   108,   109,
     235,   232,    62,    62,    62,   228,    60,    63,   122,    64,
      65,    76,   116,   186,   231,     3,    60,   189,   237,   238,
     239,   240,   241,     4,     8,     9,    10,    85,    92,    93,
      94,    99,   100,   101,   102,   103,   104,   108,   140,   141,
     142,   143,   144,   145,   146,   147,   148,   149,   150,   151,
     152,   153,   154,   155,   156,   157,   158,   159,   160,   161,
     162,   163,   164,   165,   167,   168,   169,   170,   171,   172,
     173,   174,   175,   241,   247,   249,   251,   253,   254,     3,
     211,   212,   213,   216,   219,     1,     3,    15,    16,    19,
      20,    21,    26,    27,    29,    33,    38,    44,    64,   118,
     119,   120,   121,   123,   124,   125,   126,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,   139,
     167,   178,   179,   180,   186,   192,    62,   107,   109,   163,
     197,   108,   109,   231,   235,   244,   245,    60,    65,    60,
      65,   148,   154,   148,   148,   148,   148,   148,   108,   154,
     108,   154,   108,   154,   154,     1,   167,   189,   229,    78,
      81,    82,    83,    84,    85,    86,   183,    87,   184,    90,
      91,   185,    92,    93,   181,    94,    95,    96,   182,    76,
      77,   252,    61,    65,   103,   104,   106,   107,   108,   109,
       4,    65,   214,    76,   190,   202,   221,   222,   228,   221,
      64,    64,   165,    64,   123,   108,   108,   241,   166,   167,
     108,   108,    63,   120,    79,    64,    63,   195,   197,   242,
     163,   236,   237,   244,   164,   245,   108,   109,    66,   239,
     241,   229,   229,    60,    60,   108,   235,   244,    60,   167,
     142,   144,   145,   146,   149,   150,   151,   152,   153,   148,
     163,   163,   250,   248,   163,   176,   177,   167,   212,    63,
     163,    64,   223,   224,   225,   226,   230,   231,   190,   191,
      63,   222,   191,    63,    44,   167,   166,   186,    64,    64,
     167,   167,   123,    11,   187,    65,   198,    76,   196,    61,
      60,    60,    61,   236,   164,    60,    60,    62,   148,    79,
     242,   242,    60,    65,    61,    64,    65,    79,   108,    60,
      64,   166,    60,    60,   197,    63,   197,   196,    60,    61,
     195,   140,   163,   224,   163,   227,   167,   123,   166,    64,
     123,   123,   197,    63,    65,    60,    23,    64,   166,    64,
     123,   166,    60,    60,   123,   123
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,   110,   111,   111,   111,   112,   112,   113,   113,   113,
     113,   114,   115,   115,   116,   116,   117,   117,   118,   118,
     119,   119,   120,   120,   122,   121,   121,   123,   123,   123,
     123,   123,   123,   123,   123,   123,   123,   123,   123,   124,
     125,   126,   126,   127,   127,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,   138,   139,   139,
     139,   140,   140,   141,   141,   142,   142,   143,   144,   144,
     145,   145,   146,   146,   147,   148,   148,   148,   149,   149,
     150,   150,   151,   151,   152,   152,   153,   153,   154,   154,
     154,   154,   154,   154,   154,   154,   154,   154,   154,   155,
     155,   156,   156,   157,   158,   159,   160,   161,   162,   163,
     163,   164,   164,   165,   166,   166,   167,   168,   168,   169,
     169,   169,   170,   170,   171,   171,   171,   171,   171,   171,
     172,   173,   173,   174,   175,   176,   176,   177,   177,   178,
     179,   180,   181,   181,   182,   182,   182,   183,   184,   185,
     185,   186,   186,   187,   187,   188,   188,   189,   189,   189,
     190,   190,   191,   191,   192,   192,   193,   193,   194,   194,
     195,   195,   196,   196,   197,   197,   197,   197,   197,   198,
     198,   199,   199,   200,   200,   201,   201,   201,   201,   201,
     202,   202,   202,   202,   202,   202,   202,   202,   202,   202,
     202,   202,   202,   203,   203,   204,   204,   205,   206,   206,
     207,   207,   208,   208,   209,   210,   211,   211,   212,   212,
     213,   214,   214,   216,   215,   217,   219,   218,   220,   221,
     221,   222,   223,   223,   223,   224,   224,   225,   226,   227,
     228,   228,   229,   229,   230,   230,   231,   231,   232,   232,
     232,   232,   232,   232,   233,   234,   235,   235,   236,   236,
     237,   237,   238,   238,   239,   239,   239,   240,   240,   241,
     242,   242,   243,   244,   244,   244,   245,   245,   245,   245,
     245,   246,   248,   247,   250,   249,   251,   252,   252,   253,
     253,   254,   254,   254,   254
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     1,     1,     1,     2,     1,     1,     1,
       2,     2,     3,     2,     0,     1,     1,     2,     0,     1,
       1,     2,     1,     1,     0,     4,     2,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     2,     3,
       3,     1,     1,     1,     1,     1,     5,     2,     2,     3,
       3,     1,     5,     7,     7,     5,     9,     8,     1,     1,
       1,     1,     5,     1,     3,     1,     3,     2,     1,     3,
       1,     3,     1,     3,     2,     1,     4,     6,     1,     3,
       1,     3,     1,     3,     1,     3,     1,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     4,
       2,     4,     2,     2,     2,     2,     2,     2,     2,     1,
       3,     0,     1,     1,     0,     1,     1,     1,     3,     1,
       1,     1,     3,     3,     1,     1,     1,     1,     1,     1,
       4,     1,     1,     2,     2,     0,     1,     1,     3,     1,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     3,     1,     0,     1,     0,     1,     2,     2,     2,
       2,     2,     0,     1,     1,     3,     0,     1,     1,     3,
       1,     3,     0,     1,     1,     4,     5,     4,     2,     0,
       1,     1,     2,     0,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       0,     1,     1,     1,     6,     2,     1,     3,     1,     3,
       1,     0,     1,     0,     6,     2,     0,     6,     2,     1,
       2,     3,     1,     3,     1,     1,     1,     1,     3,     1,
       1,     1,     1,     2,     0,     1,     2,     1,     1,     3,
       1,     4,     4,     3,     1,     2,     1,     2,     0,     1,
       1,     3,     1,     3,     2,     2,     1,     1,     3,     1,
       1,     1,     1,     1,     1,     2,     3,     3,     4,     3,
       4,     4,     0,     4,     0,     4,     4,     1,     1,     1,
       2,     1,     1,     1,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
/* The lookahead symbol.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex (&yylval);
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 188 "c_gram.y" /* yacc.c:1646  */
    {	if (err_cnt == 0)
			fputs("Empty source file\n", stderr);
		Parse_TOS->parse_tree= (treenode *) NULL;
		(yyval.node) = (treenode *) NULL;
	}
#line 1958 "c_gram.c" /* yacc.c:1646  */
    break;

  case 3:
#line 194 "c_gram.y" /* yacc.c:1646  */
    {
		if (err_cnt)
			fprintf(stderr,"%d errors\n",err_cnt);
		Parse_TOS->parse_tree = (yyval.node);
	}
#line 1968 "c_gram.c" /* yacc.c:1646  */
    break;

  case 4:
#line 200 "c_gram.y" /* yacc.c:1646  */
    {
		fputs("Aborting\n",stderr);
		Parse_TOS->parse_tree= (treenode *) NULL;
		YYABORT;
	}
#line 1978 "c_gram.c" /* yacc.c:1646  */
    break;

  case 6:
#line 209 "c_gram.y" /* yacc.c:1646  */
    {	if ((yyvsp[0].node))
		{	treenode *tmp_node = make_node(TN_TRANS_LIST);
			tmp_node->lnode = (yyvsp[-1].node);
			tmp_node->rnode = (yyvsp[0].node);
			(yyval.node) = tmp_node;
		} else
			(yyval.node) = (yyvsp[-1].node);
	}
#line 1991 "c_gram.c" /* yacc.c:1646  */
    break;

  case 7:
#line 220 "c_gram.y" /* yacc.c:1646  */
    {	exit_scopes(ParseStack->contxt, FILE_SCOPE);
	}
#line 1998 "c_gram.c" /* yacc.c:1646  */
    break;

  case 8:
#line 223 "c_gram.y" /* yacc.c:1646  */
    {	exit_scopes(ParseStack->contxt, FILE_SCOPE);
	}
#line 2005 "c_gram.c" /* yacc.c:1646  */
    break;

  case 10:
#line 233 "c_gram.y" /* yacc.c:1646  */
    {	free_tree((yyvsp[0].node));
		(yyval.node) = (treenode *) NULL;
	}
#line 2013 "c_gram.c" /* yacc.c:1646  */
    break;

  case 11:
#line 239 "c_gram.y" /* yacc.c:1646  */
    {	leafnode *lm, *rm = (leafnode *) 0;
		for_node *tmpnode = (for_node *) (yyvsp[-1].node);
		symentry_t *nmtbl;
		int scoped = EXTERN_SCOPE;

		tmpnode->stemnt = (yyvsp[0].node);

		if (ParseStack->contxt)
		{	rm = find_func_name((yyval.node));
			if (rm)	/* if null, an error msg was printed */
			{	lm = leftmost((yyval.node));
				if (lm && (lm->hdr.tok == STATIC))
				{	scoped = FILE_SCOPE;
					if (see_static_fcts)
					printf("static function %s\n", rm->data.sval->str);
				} else if (see_extern_fcts)
					printf("extern function %s\n", rm->data.sval->str);

				nmtbl = mk_funcdef(rm->data.sval, (yyval.node));

				nmtbl = symtab_insert_at(ParseStack->contxt->syms, nmtbl, scoped);

				rm->syment = nmtbl;	/* can replace prototype entry for real one */
				rm->syment->nes = ParseStack->contxt->syms->current;
				rm->syment->decl_level = ParseStack->contxt->syms->clevel;

				if (!nmtbl)
					yyerr("Duplicate function");

				name_scope(ParseStack->contxt,
					rm->data.sval->str,	/* fct name */
					TN_FUNC_DEF);
		}	}
		exit_scope(ParseStack->contxt);
	}
#line 2053 "c_gram.c" /* yacc.c:1646  */
    break;

  case 12:
#line 277 "c_gram.y" /* yacc.c:1646  */
    {
            for_node *tmp_node = make_for(TN_FUNC_DEF);

            tmp_node->init = (yyvsp[-2].node);
            tmp_node->test = (yyvsp[-1].node);
            tmp_node->incr = (yyvsp[0].node);
            add_params_to_symtab((yyvsp[-1].node));
            (yyval.node) = (treenode *) tmp_node;
	}
#line 2067 "c_gram.c" /* yacc.c:1646  */
    break;

  case 13:
#line 287 "c_gram.y" /* yacc.c:1646  */
    {
            /* return type defaults to int */
            for_node *tmp_node = make_for(TN_FUNC_DEF);

            tmp_node->init = (treenode *) NULL;
            tmp_node->test = (yyvsp[-1].node);
            tmp_node->incr = (yyvsp[0].node);
            add_params_to_symtab((yyvsp[-1].node));
            (yyval.node) = (treenode *) tmp_node;
	}
#line 2082 "c_gram.c" /* yacc.c:1646  */
    break;

  case 14:
#line 300 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 2090 "c_gram.c" /* yacc.c:1646  */
    break;

  case 17:
#line 308 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_DECL_LIST);
            tmp_node->lnode = (yyvsp[-1].node);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2101 "c_gram.c" /* yacc.c:1646  */
    break;

  case 18:
#line 323 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 2109 "c_gram.c" /* yacc.c:1646  */
    break;

  case 21:
#line 331 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_DECL_LIST); /* should be TN_BLOCK_LIST? */
            tmp_node->lnode = (yyvsp[-1].node);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2120 "c_gram.c" /* yacc.c:1646  */
    break;

  case 24:
#line 344 "c_gram.y" /* yacc.c:1646  */
    {
            enter_scope(ParseStack->contxt);
	}
#line 2128 "c_gram.c" /* yacc.c:1646  */
    break;

  case 25:
#line 348 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-3].node)->hdr.type = TN_BLOCK;
            (yyvsp[-3].node)->lnode = (yyvsp[-1].node);
            (yyvsp[-3].node)->rnode = NULL;
            free_tree((yyvsp[0].node));
            exit_scope(ParseStack->contxt);
	}
#line 2140 "c_gram.c" /* yacc.c:1646  */
    break;

  case 26:
#line 356 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
            free_tree((yyvsp[0].node));
	}
#line 2149 "c_gram.c" /* yacc.c:1646  */
    break;

  case 27:
#line 363 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2159 "c_gram.c" /* yacc.c:1646  */
    break;

  case 28:
#line 369 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2169 "c_gram.c" /* yacc.c:1646  */
    break;

  case 29:
#line 375 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2179 "c_gram.c" /* yacc.c:1646  */
    break;

  case 30:
#line 381 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2189 "c_gram.c" /* yacc.c:1646  */
    break;

  case 31:
#line 387 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2199 "c_gram.c" /* yacc.c:1646  */
    break;

  case 32:
#line 393 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2209 "c_gram.c" /* yacc.c:1646  */
    break;

  case 33:
#line 399 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2219 "c_gram.c" /* yacc.c:1646  */
    break;

  case 34:
#line 405 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2229 "c_gram.c" /* yacc.c:1646  */
    break;

  case 35:
#line 411 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2239 "c_gram.c" /* yacc.c:1646  */
    break;

  case 36:
#line 417 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2249 "c_gram.c" /* yacc.c:1646  */
    break;

  case 37:
#line 423 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = (yyvsp[0].node);
            (yyval.node) = tmp_node;
	}
#line 2259 "c_gram.c" /* yacc.c:1646  */
    break;

  case 38:
#line 429 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
            free_tree((yyvsp[0].node));
	}
#line 2268 "c_gram.c" /* yacc.c:1646  */
    break;

  case 39:
#line 436 "c_gram.y" /* yacc.c:1646  */
    {
            free_tree((yyvsp[-1].node));
	}
#line 2276 "c_gram.c" /* yacc.c:1646  */
    break;

  case 40:
#line 442 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_LABEL;
            (yyvsp[-1].node)->lnode = (treenode *) (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2287 "c_gram.c" /* yacc.c:1646  */
    break;

  case 46:
#line 460 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-4].node)->hdr.type = TN_SWITCH;
            (yyvsp[-4].node)->lnode = (treenode *) (yyvsp[-2].node);
            (yyvsp[-4].node)->rnode = (treenode *) (yyvsp[0].node);
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2299 "c_gram.c" /* yacc.c:1646  */
    break;

  case 47:
#line 470 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_JUMP;
            free_tree((yyvsp[0].node));
	}
#line 2308 "c_gram.c" /* yacc.c:1646  */
    break;

  case 48:
#line 477 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_JUMP;
            free_tree((yyvsp[0].node));
	}
#line 2317 "c_gram.c" /* yacc.c:1646  */
    break;

  case 49:
#line 484 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_JUMP;
            (yyvsp[-2].node)->lnode = (yyvsp[-1].node);
            free_tree((yyvsp[0].node));
	}
#line 2327 "c_gram.c" /* yacc.c:1646  */
    break;

  case 50:
#line 492 "c_gram.y" /* yacc.c:1646  */
    {
		if (ParseStack->contxt)
		{	symentry_t *nmtbl, *y;
			nmtbl = mk_label((yyvsp[-1].leaf)->data.sval, (yyval.node));

			y = symtab_insert_at(ParseStack->contxt->labels,
					nmtbl, FUNCTION_SCOPE);
			if (!y)
				printf("not really a Duplicate label\n");

			(yyvsp[-1].leaf)->syment = y;
		}

		if (0) printf("goto %s, $2=%s (%p)\n",
			(yyvsp[-1].leaf)->data.sval->str,
			name_of_node((yyvsp[-1].leaf)->hdr.type),
			(yyvsp[-1].leaf)->syment);


            (yyvsp[-2].node)->hdr.type = TN_JUMP;
            (yyvsp[-2].node)->lnode = (treenode *) (yyvsp[-1].leaf);
            free_tree((yyvsp[0].node));
	}
#line 2355 "c_gram.c" /* yacc.c:1646  */
    break;

  case 51:
#line 518 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
            free_tree((yyvsp[0].node));
	}
#line 2364 "c_gram.c" /* yacc.c:1646  */
    break;

  case 52:
#line 525 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-4].ifn)->hdr.type = TN_IF;
            (yyvsp[-4].ifn)->cond = (yyvsp[-2].node);
            (yyvsp[-4].ifn)->then_n = (yyvsp[0].node);
            (yyval.node) = (treenode *) (yyvsp[-4].ifn);
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2377 "c_gram.c" /* yacc.c:1646  */
    break;

  case 53:
#line 536 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-6].ifn)->hdr.type = TN_IF;
            (yyvsp[-6].ifn)->cond = (yyvsp[-4].node);
            (yyvsp[-6].ifn)->then_n = (yyvsp[-2].node);
            (yyvsp[-6].ifn)->else_n = (yyvsp[0].node);
            (yyval.node) = (treenode *) (yyvsp[-6].ifn);
            free_tree((yyvsp[-5].node));
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2392 "c_gram.c" /* yacc.c:1646  */
    break;

  case 54:
#line 549 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-6].node)->hdr.type = TN_DOWHILE;
            (yyvsp[-6].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-6].node)->rnode = (yyvsp[-5].node);
            free_tree((yyvsp[-4].node));
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
            free_tree((yyvsp[0].node));
	}
#line 2406 "c_gram.c" /* yacc.c:1646  */
    break;

  case 55:
#line 561 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-4].node)->hdr.type = TN_WHILE;
            (yyvsp[-4].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-4].node)->rnode = (yyvsp[0].node);
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2418 "c_gram.c" /* yacc.c:1646  */
    break;

  case 56:
#line 572 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-8].forn)->hdr.type = TN_FOR;
            (yyvsp[-8].forn)->init = (yyvsp[-6].node);
            (yyvsp[-8].forn)->test = (yyvsp[-4].node);
            (yyvsp[-8].forn)->incr = (yyvsp[-2].node);
            (yyvsp[-8].forn)->stemnt = (yyvsp[0].node);
            free_tree((yyvsp[-7].node));
            free_tree((yyvsp[-5].node));
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2434 "c_gram.c" /* yacc.c:1646  */
    break;

  case 57:
#line 585 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-7].forn)->hdr.type = TN_FOR;
            (yyvsp[-7].forn)->init = (yyvsp[-5].node);
            (yyvsp[-7].forn)->test = (yyvsp[-4].node);
            (yyvsp[-7].forn)->incr = (yyvsp[-2].node);
            (yyvsp[-7].forn)->stemnt = (yyvsp[0].node);
            free_tree((yyvsp[-6].node));
            free_tree((yyvsp[-5].node));
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2450 "c_gram.c" /* yacc.c:1646  */
    break;

  case 62:
#line 606 "c_gram.y" /* yacc.c:1646  */
    {
            if_node *tmpnode = make_if(TN_COND_EXPR);
		tmpnode->hdr.tok = QUESTMARK;
            tmpnode->cond = (yyvsp[-4].node);
            tmpnode->then_n = (yyvsp[-2].node);
            tmpnode->else_n = (yyvsp[0].node);
            (yyval.node) = (treenode *) tmpnode;
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
	}
#line 2465 "c_gram.c" /* yacc.c:1646  */
    break;

  case 64:
#line 620 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2476 "c_gram.c" /* yacc.c:1646  */
    break;

  case 66:
#line 630 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2487 "c_gram.c" /* yacc.c:1646  */
    break;

  case 67:
#line 639 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2496 "c_gram.c" /* yacc.c:1646  */
    break;

  case 69:
#line 647 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2507 "c_gram.c" /* yacc.c:1646  */
    break;

  case 71:
#line 657 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2518 "c_gram.c" /* yacc.c:1646  */
    break;

  case 73:
#line 667 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2529 "c_gram.c" /* yacc.c:1646  */
    break;

  case 74:
#line 676 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2538 "c_gram.c" /* yacc.c:1646  */
    break;

  case 76:
#line 684 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-3].node)->hdr.type = TN_CAST;
            (yyvsp[-3].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-3].node)->rnode = (yyvsp[0].node);
            free_tree((yyvsp[-1].node));
	}
#line 2549 "c_gram.c" /* yacc.c:1646  */
    break;

  case 77:
#line 691 "c_gram.y" /* yacc.c:1646  */
    {	/* rsc don't choke on struct constructors */
	    (yyvsp[-5].node)->hdr.type = TN_CAST;
	    (yyvsp[-5].node)->lnode = (yyvsp[-4].node);
	    (yyvsp[-5].node)->rnode = (yyvsp[-1].node);
	    free_tree((yyvsp[-3].node));
	    free_tree((yyvsp[-2].node));
	    free_tree((yyvsp[0].node));
	}
#line 2562 "c_gram.c" /* yacc.c:1646  */
    break;

  case 79:
#line 703 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2573 "c_gram.c" /* yacc.c:1646  */
    break;

  case 81:
#line 713 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2584 "c_gram.c" /* yacc.c:1646  */
    break;

  case 83:
#line 723 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2595 "c_gram.c" /* yacc.c:1646  */
    break;

  case 85:
#line 733 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2606 "c_gram.c" /* yacc.c:1646  */
    break;

  case 87:
#line 743 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2617 "c_gram.c" /* yacc.c:1646  */
    break;

  case 99:
#line 765 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-3].node)->hdr.type = TN_EXPR;
            (yyvsp[-3].node)->rnode = (yyvsp[-1].node);
            free_tree((yyvsp[-2].node));
            free_tree((yyvsp[0].node));
	}
#line 2628 "c_gram.c" /* yacc.c:1646  */
    break;

  case 100:
#line 772 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2637 "c_gram.c" /* yacc.c:1646  */
    break;

  case 101:
#line 779 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-3].node)->hdr.type = TN_EXPR;
            (yyvsp[-3].node)->rnode = (yyvsp[-1].node);
            free_tree((yyvsp[-2].node));
            free_tree((yyvsp[0].node));
	}
#line 2648 "c_gram.c" /* yacc.c:1646  */
    break;

  case 102:
#line 786 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2657 "c_gram.c" /* yacc.c:1646  */
    break;

  case 103:
#line 793 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2666 "c_gram.c" /* yacc.c:1646  */
    break;

  case 104:
#line 800 "c_gram.y" /* yacc.c:1646  */
    {
            /* Unary plus is an ISO addition (for symmetry) - ignore it */
            (yyval.node) = (yyvsp[0].node);
            free_tree((yyvsp[-1].node));
	}
#line 2676 "c_gram.c" /* yacc.c:1646  */
    break;

  case 105:
#line 808 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2685 "c_gram.c" /* yacc.c:1646  */
    break;

  case 106:
#line 815 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_DEREF;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2694 "c_gram.c" /* yacc.c:1646  */
    break;

  case 107:
#line 822 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2703 "c_gram.c" /* yacc.c:1646  */
    break;

  case 108:
#line 829 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 2712 "c_gram.c" /* yacc.c:1646  */
    break;

  case 110:
#line 837 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_ASSIGN;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 2723 "c_gram.c" /* yacc.c:1646  */
    break;

  case 111:
#line 846 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 2731 "c_gram.c" /* yacc.c:1646  */
    break;

  case 114:
#line 856 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 2739 "c_gram.c" /* yacc.c:1646  */
    break;

  case 118:
#line 867 "c_gram.y" /* yacc.c:1646  */
    {
           (yyvsp[-1].node)->hdr.type = TN_EXPR;
           (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
           (yyvsp[-1].node)->rnode = (yyvsp[0].node);
           (yyval.node) = (yyvsp[-1].node);
	}
#line 2750 "c_gram.c" /* yacc.c:1646  */
    break;

  case 119:
#line 876 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 2758 "c_gram.c" /* yacc.c:1646  */
    break;

  case 121:
#line 881 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 2766 "c_gram.c" /* yacc.c:1646  */
    break;

  case 122:
#line 887 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (yyvsp[-1].node);
           free_tree((yyvsp[-2].node));
           free_tree((yyvsp[0].node));
	}
#line 2776 "c_gram.c" /* yacc.c:1646  */
    break;

  case 123:
#line 893 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
           free_tree((yyvsp[-2].node));
           free_tree((yyvsp[0].node));
	}
#line 2786 "c_gram.c" /* yacc.c:1646  */
    break;

  case 130:
#line 909 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_INDEX;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 2798 "c_gram.c" /* yacc.c:1646  */
    break;

  case 133:
#line 923 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[0].node)->hdr.type = TN_EXPR;
            (yyvsp[0].node)->lnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[0].node);
	}
#line 2808 "c_gram.c" /* yacc.c:1646  */
    break;

  case 134:
#line 931 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[0].node)->hdr.type = TN_EXPR;
            (yyvsp[0].node)->lnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[0].node);
	}
#line 2818 "c_gram.c" /* yacc.c:1646  */
    break;

  case 135:
#line 939 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 2826 "c_gram.c" /* yacc.c:1646  */
    break;

  case 138:
#line 947 "c_gram.y" /* yacc.c:1646  */
    {
	    if((yyvsp[-1].node) == 0){
		(yyval.node) = (yyvsp[-2].node);
	    }else{
                (yyvsp[-1].node)->hdr.type = TN_EXPR_LIST;
                (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
                (yyvsp[-1].node)->rnode = (yyvsp[0].node);
                (yyval.node) = (yyvsp[-1].node);
	    }
	}
#line 2841 "c_gram.c" /* yacc.c:1646  */
    break;

  case 139:
#line 960 "c_gram.y" /* yacc.c:1646  */
    {
		(yyval.node) = (treenode *) (yyvsp[0].leaf);
		if (ParseStack->contxt)
		{	symentry_t *nmtbl, *y;
			nmtbl = mk_label((yyvsp[0].leaf)->data.sval, (yyval.node));

			if (0) printf("named label %s %p\n", (yyvsp[0].leaf)->data.sval->str, nmtbl);

			y = symtab_insert_at(ParseStack->contxt->labels,
					nmtbl, FUNCTION_SCOPE);
			if (!y)
				yyerr("Duplicate label.");

	/*		$$->syment = y;	*/
		}
	}
#line 2862 "c_gram.c" /* yacc.c:1646  */
    break;

  case 140:
#line 979 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_EXPR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (treenode *) (yyvsp[-1].node);
	}
#line 2872 "c_gram.c" /* yacc.c:1646  */
    break;

  case 151:
#line 1009 "c_gram.y" /* yacc.c:1646  */
    {
            leafnode *lm;
            (yyvsp[0].node)->hdr.type = TN_DECL;
            (yyvsp[0].node)->lnode = (yyvsp[-2].node);
            (yyvsp[0].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[0].node);

            lm = leftmost((yyval.node));
            if (lm)
            {	if (lm->hdr.tok == TYPEDEF)
		{	/* Decl is a typedef. Scan the subtree for the
			   ident naming the new type.  Don't use rightmost()
			   since it doesn't give the ident for complex
			   types (like arrays).
			 */
			find_typedef_name((yyval.node),(yyval.node),insert_typedef);
		} else
		{	/* Find the identifier for a normal declaration. */
			find_ident_name((yyval.node),(yyval.node),NULL,insert_decl);
		}
            }
	}
#line 2899 "c_gram.c" /* yacc.c:1646  */
    break;

  case 152:
#line 1032 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 2907 "c_gram.c" /* yacc.c:1646  */
    break;

  case 153:
#line 1038 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 2915 "c_gram.c" /* yacc.c:1646  */
    break;

  case 154:
#line 1042 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 2923 "c_gram.c" /* yacc.c:1646  */
    break;

  case 155:
#line 1048 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 2931 "c_gram.c" /* yacc.c:1646  */
    break;

  case 157:
#line 1055 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 2942 "c_gram.c" /* yacc.c:1646  */
    break;

  case 158:
#line 1062 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 2953 "c_gram.c" /* yacc.c:1646  */
    break;

  case 159:
#line 1069 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 2964 "c_gram.c" /* yacc.c:1646  */
    break;

  case 160:
#line 1078 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 2975 "c_gram.c" /* yacc.c:1646  */
    break;

  case 161:
#line 1085 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 2986 "c_gram.c" /* yacc.c:1646  */
    break;

  case 162:
#line 1094 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 2994 "c_gram.c" /* yacc.c:1646  */
    break;

  case 165:
#line 1102 "c_gram.y" /* yacc.c:1646  */
    {
           (yyvsp[-1].node)->hdr.type = TN_ASSIGN;
           (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
           (yyvsp[-1].node)->rnode = (yyvsp[0].node);
           (yyval.node) = (yyvsp[-1].node);
	}
#line 3005 "c_gram.c" /* yacc.c:1646  */
    break;

  case 166:
#line 1111 "c_gram.y" /* yacc.c:1646  */
    {
          (yyval.node) = (treenode *) NULL;
	}
#line 3013 "c_gram.c" /* yacc.c:1646  */
    break;

  case 169:
#line 1119 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_DECLS;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3024 "c_gram.c" /* yacc.c:1646  */
    break;

  case 171:
#line 1129 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_INIT_LIST;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3035 "c_gram.c" /* yacc.c:1646  */
    break;

  case 172:
#line 1137 "c_gram.y" /* yacc.c:1646  */
    { }
#line 3041 "c_gram.c" /* yacc.c:1646  */
    break;

  case 173:
#line 1138 "c_gram.y" /* yacc.c:1646  */
    { }
#line 3047 "c_gram.c" /* yacc.c:1646  */
    break;

  case 175:
#line 1143 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_INIT_BLK;
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[-1].node));
            free_tree((yyvsp[0].node));
	}
#line 3059 "c_gram.c" /* yacc.c:1646  */
    break;

  case 176:
#line 1151 "c_gram.y" /* yacc.c:1646  */
    {	(yyval.node) = (yyvsp[0].node);
	}
#line 3066 "c_gram.c" /* yacc.c:1646  */
    break;

  case 177:
#line 1154 "c_gram.y" /* yacc.c:1646  */
    {	(yyval.node) = (yyvsp[0].node);
	}
#line 3073 "c_gram.c" /* yacc.c:1646  */
    break;

  case 178:
#line 1157 "c_gram.y" /* yacc.c:1646  */
    {	(yyval.node)->hdr.type = TN_INIT_LIST;			/* gjh allow empty list */
		(yyval.node)->lnode = 0;
		(yyval.node)->rnode = 0;
  	}
#line 3082 "c_gram.c" /* yacc.c:1646  */
    break;

  case 179:
#line 1164 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 3090 "c_gram.c" /* yacc.c:1646  */
    break;

  case 182:
#line 1172 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3101 "c_gram.c" /* yacc.c:1646  */
    break;

  case 183:
#line 1181 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 3109 "c_gram.c" /* yacc.c:1646  */
    break;

  case 207:
#line 1218 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 3117 "c_gram.c" /* yacc.c:1646  */
    break;

  case 210:
#line 1228 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 3125 "c_gram.c" /* yacc.c:1646  */
    break;

  case 212:
#line 1235 "c_gram.y" /* yacc.c:1646  */
    {
          (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 3133 "c_gram.c" /* yacc.c:1646  */
    break;

  case 214:
#line 1242 "c_gram.y" /* yacc.c:1646  */
    {
		(yyvsp[-5].node)->hdr.type = TN_OBJ_DEF;
		(yyvsp[-5].node)->lnode = (yyvsp[-4].node);
		(yyvsp[-5].node)->rnode = (yyvsp[-2].node);
		free_tree((yyvsp[-3].node));
		free_tree((yyvsp[-1].node));
		free_tree((yyvsp[0].node));

		if (ParseStack->contxt && (yyvsp[-4].node))
		{	leafnode *leaf = (leafnode *) (yyvsp[-4].node);
			symentry_t *nmtbl;

			nmtbl = mk_tag(leaf->data.sval, (yyval.node));	/* enum name */

			if (leaf->syment)
			{	location((yyvsp[-4].node));
				printf("typename redefined: '%s'\n", leaf->syment->nme->str);
			}
			leaf->syment = nmtbl;
			if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
				yyerr("Duplicate tag.");
			leaf->syment->nes = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
		}
	}
#line 3163 "c_gram.c" /* yacc.c:1646  */
    break;

  case 215:
#line 1270 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_OBJ_REF;
            (yyvsp[-1].node)->lnode = (yyvsp[0].node);
	}
#line 3172 "c_gram.c" /* yacc.c:1646  */
    break;

  case 217:
#line 1278 "c_gram.y" /* yacc.c:1646  */
    {
           (yyvsp[-1].node)->hdr.type = TN_ENUM_LIST;
           (yyvsp[-1].node)->lnode = (treenode *) (yyvsp[-2].node);
           (yyvsp[-1].node)->rnode = (yyvsp[0].node);
           (yyval.node) = (yyvsp[-1].node);
	}
#line 3183 "c_gram.c" /* yacc.c:1646  */
    break;

  case 219:
#line 1288 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_ASSIGN;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3194 "c_gram.c" /* yacc.c:1646  */
    break;

  case 220:
#line 1297 "c_gram.y" /* yacc.c:1646  */
    {
		(yyval.node) = (treenode *) (yyvsp[0].leaf);
		if (ParseStack->contxt)
		{	symentry_t *nmtbl = mk_enum_const((yyvsp[0].leaf)->data.sval, (yyval.node));

			add_constant(nmtbl->nme->str);  /* gjh */

			if (!symtab_insert(ParseStack->contxt->syms, nmtbl))
				yyerr("Duplicate enumeration constant.");
		}
	}
#line 3210 "c_gram.c" /* yacc.c:1646  */
    break;

  case 221:
#line 1311 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (treenode *) NULL;
	}
#line 3218 "c_gram.c" /* yacc.c:1646  */
    break;

  case 223:
#line 1318 "c_gram.y" /* yacc.c:1646  */
    {
            enter_scope(ParseStack->contxt);
	}
#line 3226 "c_gram.c" /* yacc.c:1646  */
    break;

  case 224:
#line 1322 "c_gram.y" /* yacc.c:1646  */
    {
		(yyvsp[-5].node)->hdr.type = TN_OBJ_DEF;
		(yyvsp[-5].node)->lnode = (yyvsp[-4].node);
		(yyvsp[-5].node)->rnode = (yyvsp[-1].node);
		free_tree((yyvsp[-3].node));
		free_tree((yyvsp[0].node));
		if (ParseStack->contxt && (yyvsp[-4].node))
		{	leafnode *leaf = (leafnode *) (yyvsp[-4].node);
			symentry_t *nmtbl;

			nmtbl = mk_tag(leaf->data.sval, (yyval.node));
			leaf->syment = nmtbl;

			/**** 4.9.4   tag names shall be in all lowercase letters and underscores */
			if (!exclude_location((yyvsp[-4].node))
			&&  has_upper(leaf->syment->nme->str))
			{	location((yyvsp[-4].node));
				printf("tag name '%s' has uppercase characters\n", leaf->syment->nme->str);
			}

			if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
				yyerr("Duplicate tag.");

			leaf->syment->nes = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
		}
    
		find_components((yyvsp[-1].node),(yyvsp[-5].node),(yyvsp[-5].node),insert_component);
		name_scope(ParseStack->contxt,
			(yyvsp[-4].node)?((leafnode *) (yyvsp[-4].node))->data.sval->str:"-UnNamed-", TN_OBJ_DEF);
		exit_scope(ParseStack->contxt);
	}
#line 3263 "c_gram.c" /* yacc.c:1646  */
    break;

  case 225:
#line 1357 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_OBJ_REF;
            (yyvsp[-1].node)->lnode = (yyvsp[0].node);
	}
#line 3272 "c_gram.c" /* yacc.c:1646  */
    break;

  case 226:
#line 1364 "c_gram.y" /* yacc.c:1646  */
    {
            enter_scope(ParseStack->contxt);
	}
#line 3280 "c_gram.c" /* yacc.c:1646  */
    break;

  case 227:
#line 1368 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-5].node)->hdr.type = TN_OBJ_DEF;
            (yyvsp[-5].node)->lnode = (yyvsp[-4].node);
            (yyvsp[-5].node)->rnode = (yyvsp[-1].node);
            free_tree((yyvsp[-3].node));
            free_tree((yyvsp[0].node));
            if (ParseStack->contxt && (yyvsp[-4].node))
            {	leafnode *leaf = (leafnode *) (yyvsp[-4].node);
		symentry_t *nmtbl;

		nmtbl = mk_tag(leaf->data.sval, (yyval.node));
		leaf->syment = nmtbl;

		/**** 4.9.4   tag names shall be in all lowercase letters and underscores */
		if (!exclude_location((yyvsp[-4].node)) && has_upper(leaf->syment->nme->str))
		{	location((yyvsp[-4].node));
			printf("tag name '%s' has uppercase characters\n", leaf->syment->nme->str);
		}

            	if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
			yyerr("Duplicate tag.");

		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
            }

            find_components((yyvsp[-1].node),(yyvsp[-5].node),(yyvsp[-5].node),insert_component);
		if ((yyvsp[-4].node))
		{
		name_scope(ParseStack->contxt,
			((leafnode *) (yyvsp[-4].node))->data.sval->str,
			TN_OBJ_DEF);
		}
            exit_scope(ParseStack->contxt);
	}
#line 3320 "c_gram.c" /* yacc.c:1646  */
    break;

  case 228:
#line 1406 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_OBJ_REF;
            (yyvsp[-1].node)->lnode = (yyvsp[0].node);
	}
#line 3329 "c_gram.c" /* yacc.c:1646  */
    break;

  case 230:
#line 1414 "c_gram.y" /* yacc.c:1646  */
    {
           treenode *tmpnode = make_node(TN_FIELD_LIST);
           tmpnode->lnode = (yyvsp[-1].node);
           tmpnode->rnode = (yyvsp[0].node);
           (yyval.node) = tmpnode;
	}
#line 3340 "c_gram.c" /* yacc.c:1646  */
    break;

  case 231:
#line 1423 "c_gram.y" /* yacc.c:1646  */
    {
          (yyvsp[0].node)->hdr.type = TN_COMP_DECL;
          (yyvsp[0].node)->lnode = (yyvsp[-2].node);
          (yyvsp[0].node)->rnode = (yyvsp[-1].node);
          (yyval.node) = (yyvsp[0].node);
	}
#line 3351 "c_gram.c" /* yacc.c:1646  */
    break;

  case 233:
#line 1433 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_DECLS;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3362 "c_gram.c" /* yacc.c:1646  */
    break;

  case 234:
#line 1440 "c_gram.y" /* yacc.c:1646  */
    {	extern FILE *yyin;
		ungetc(';', yyin);
		(yyval.node) = (treenode *) 0;
	}
#line 3371 "c_gram.c" /* yacc.c:1646  */
    break;

  case 238:
#line 1454 "c_gram.y" /* yacc.c:1646  */
    {
#if 0
            (yyvsp[-1].node)->hdr.type = TN_BIT_FIELD;	/* gjh: not recognized where needed */
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
#else
		(yyval.node) = (yyvsp[-2].node);
#endif
	}
#line 3386 "c_gram.c" /* yacc.c:1646  */
    break;

  case 242:
#line 1474 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_NME);
            tmpnode->lnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3396 "c_gram.c" /* yacc.c:1646  */
    break;

  case 243:
#line 1480 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_TYPE_NME);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3407 "c_gram.c" /* yacc.c:1646  */
    break;

  case 244:
#line 1489 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 3415 "c_gram.c" /* yacc.c:1646  */
    break;

  case 246:
#line 1496 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3426 "c_gram.c" /* yacc.c:1646  */
    break;

  case 248:
#line 1506 "c_gram.y" /* yacc.c:1646  */
    {	/* gjh: was simple_decl - should be field_ident
		 * to allow typedef'ed names as identifiers
		 * but this introduces 5 shift reduce and 23 reduce/reduce conflicts
		 */
		(yyval.node) = (yyvsp[0].node);
	}
#line 3437 "c_gram.c" /* yacc.c:1646  */
    break;

  case 249:
#line 1513 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (yyvsp[-1].node);
            free_tree((yyvsp[-2].node));
            free_tree((yyvsp[0].node));
	}
#line 3447 "c_gram.c" /* yacc.c:1646  */
    break;

  case 251:
#line 1520 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_FUNC_DECL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3459 "c_gram.c" /* yacc.c:1646  */
    break;

  case 252:
#line 1528 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_FUNC_DECL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3471 "c_gram.c" /* yacc.c:1646  */
    break;

  case 253:
#line 1536 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_FUNC_DECL;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyval.node) = (yyvsp[-1].node);
            free_tree((yyvsp[0].node));
	}
#line 3482 "c_gram.c" /* yacc.c:1646  */
    break;

  case 254:
#line 1545 "c_gram.y" /* yacc.c:1646  */
    {
	/* NYI - Need error check code here
           leafnode *ln = $1;
           fprintf(stdout,"Value: %s\n", nmestr(ln->data.sval));
	*/
	}
#line 3493 "c_gram.c" /* yacc.c:1646  */
    break;

  case 255:
#line 1554 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_PNTR;
            (yyvsp[-1].node)->lnode = (yyvsp[0].node);
            (yyvsp[-1].node)->rnode = NULL;
	}
#line 3503 "c_gram.c" /* yacc.c:1646  */
    break;

  case 257:
#line 1563 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_PNTR;
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
	}
#line 3512 "c_gram.c" /* yacc.c:1646  */
    break;

  case 258:
#line 1570 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) NULL;
	}
#line 3520 "c_gram.c" /* yacc.c:1646  */
    break;

  case 261:
#line 1578 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_PARAM_LIST;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3531 "c_gram.c" /* yacc.c:1646  */
    break;

  case 263:
#line 1588 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_PARAM_LIST;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (yyvsp[0].node);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3542 "c_gram.c" /* yacc.c:1646  */
    break;

  case 264:
#line 1597 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3553 "c_gram.c" /* yacc.c:1646  */
    break;

  case 265:
#line 1604 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3564 "c_gram.c" /* yacc.c:1646  */
    break;

  case 266:
#line 1611 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3574 "c_gram.c" /* yacc.c:1646  */
    break;

  case 267:
#line 1619 "c_gram.y" /* yacc.c:1646  */
    {
           (yyval.node) = (treenode *) (yyvsp[0].leaf);
	}
#line 3582 "c_gram.c" /* yacc.c:1646  */
    break;

  case 268:
#line 1623 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-1].node)->hdr.type = TN_IDENT_LIST;
            (yyvsp[-1].node)->lnode = (yyvsp[-2].node);
            (yyvsp[-1].node)->rnode = (treenode *) (yyvsp[0].leaf);
            (yyval.node) = (yyvsp[-1].node);
	}
#line 3593 "c_gram.c" /* yacc.c:1646  */
    break;

  case 272:
#line 1639 "c_gram.y" /* yacc.c:1646  */
    { 
            (yyvsp[0].node)->hdr.type = TN_IDENT;
            (yyvsp[0].node)->hdr.tok  = IDENT;	/* convert TYPEDEF_NAME into IDENT */
#if 0
	    (yyvsp[0].node)->hdr.udefined = 1;	/* gjh: remember origin */
#endif
            (yyval.node) = (treenode *) (yyvsp[0].node);
	}
#line 3606 "c_gram.c" /* yacc.c:1646  */
    break;

  case 274:
#line 1651 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3616 "c_gram.c" /* yacc.c:1646  */
    break;

  case 275:
#line 1657 "c_gram.y" /* yacc.c:1646  */
    {
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = (yyvsp[-1].node);
            tmpnode->rnode = (yyvsp[0].node);
            (yyval.node) = tmpnode;
	}
#line 3627 "c_gram.c" /* yacc.c:1646  */
    break;

  case 276:
#line 1666 "c_gram.y" /* yacc.c:1646  */
    {
            (yyval.node) = (yyvsp[-1].node);
            free_tree((yyvsp[-2].node));
            free_tree((yyvsp[0].node));
	}
#line 3637 "c_gram.c" /* yacc.c:1646  */
    break;

  case 277:
#line 1672 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_ARRAY_DECL;
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            free_tree((yyvsp[0].node));
	}
#line 3647 "c_gram.c" /* yacc.c:1646  */
    break;

  case 278:
#line 1678 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_ARRAY_DECL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3659 "c_gram.c" /* yacc.c:1646  */
    break;

  case 279:
#line 1686 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_FUNC_DECL;
            (yyvsp[-1].node)->rnode = (yyvsp[-1].node);
            free_tree((yyvsp[0].node));
	}
#line 3669 "c_gram.c" /* yacc.c:1646  */
    break;

  case 280:
#line 1692 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_FUNC_DECL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3681 "c_gram.c" /* yacc.c:1646  */
    break;

  case 281:
#line 1702 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_ARRAY_DECL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3693 "c_gram.c" /* yacc.c:1646  */
    break;

  case 282:
#line 1712 "c_gram.y" /* yacc.c:1646  */
    {   /* gjh */ structfieldflag = 1;
	}
#line 3700 "c_gram.c" /* yacc.c:1646  */
    break;

  case 283:
#line 1715 "c_gram.y" /* yacc.c:1646  */
    {   /* gjh */ structfieldflag = 0;
	
            (yyvsp[-2].node)->hdr.type = TN_SELECT;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (treenode *) (yyvsp[0].node);
            (yyval.node) = (yyvsp[-2].node);
	}
#line 3712 "c_gram.c" /* yacc.c:1646  */
    break;

  case 284:
#line 1725 "c_gram.y" /* yacc.c:1646  */
    {   /* gjh */ structfieldflag = 1;
	}
#line 3719 "c_gram.c" /* yacc.c:1646  */
    break;

  case 285:
#line 1728 "c_gram.y" /* yacc.c:1646  */
    {   /* gjh */ structfieldflag = 0;
	
            (yyvsp[-2].node)->hdr.type = TN_SELECT;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (treenode *) (yyvsp[0].node);
            (yyval.node) = (yyvsp[-2].node);
	}
#line 3731 "c_gram.c" /* yacc.c:1646  */
    break;

  case 286:
#line 1738 "c_gram.y" /* yacc.c:1646  */
    {
            (yyvsp[-2].node)->hdr.type = TN_FUNC_CALL;
            (yyvsp[-2].node)->lnode = (yyvsp[-3].node);
            (yyvsp[-2].node)->rnode = (yyvsp[-1].node);
            (yyval.node) = (yyvsp[-2].node);
            free_tree((yyvsp[0].node));
	}
#line 3743 "c_gram.c" /* yacc.c:1646  */
    break;

  case 290:
#line 1753 "c_gram.y" /* yacc.c:1646  */
    {
#if 0
		leafnode *ln;
		ln->data.str = emalloc(strlen((yyvsp[-1].leaf)->data.str)+strlen((yyvsp[0].leaf)->data.str)+1);
		strcpy(ln->data.str, (yyvsp[-1].leaf)->data.str);
		strcat(ln->data.str, (yyvsp[0].leaf)->data.str);
		(yyvsp[0].leaf)->data.str = ln->data.str;
#endif
		(yyval.leaf) = (yyvsp[0].leaf);
	}
#line 3758 "c_gram.c" /* yacc.c:1646  */
    break;


#line 3762 "c_gram.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 1771 "c_gram.y" /* yacc.c:1906  */


static int
is_func_proto(treenode *t)
{
	if (!t) return 0;

	if (t->hdr.type == TN_FUNC_DECL)
		return 1;

	if (t->hdr.which == NODE_T
	&&  (t->hdr.type == TN_FUNC_DEF || t->hdr.type == TN_DECL))	/* jerry james 8/18/04 */
		return is_func_proto(t->lnode) || is_func_proto(t->rnode);

	return 0;
}

typedef struct Recorded Recorded;

struct Recorded {
	char	*fct;
	char	*fnm;
	int	isstatic;
	Recorded	*nxt;
};

static Recorded *recorded;

static void
record_fct_name(char *s, int tok, char *f)
{	Recorded *r;

	for (r = recorded; r; r = r->nxt)
		if (strcmp(r->fct, s) == 0
		&&  r->isstatic == tok
		&&  strcmp(r->fnm, f) == 0)
			return;

	r = (Recorded *) emalloc(sizeof(Recorded));
	r->fct = (char *) emalloc(strlen(s)+1);
	strcpy(r->fct, s);
	r->fnm = (char *) emalloc(strlen(f)+1);
	strcpy(r->fnm, f);
	r->isstatic = tok;
	r->nxt = recorded;
	recorded = r;
}

extern int
is_recorded(char *s, char *f)
{	Recorded *r;

	for (r = recorded; r; r = r->nxt)
		if (strcmp(r->fct, s) == 0
		&&  (r->isstatic == 0 || strcmp(r->fnm, f) == 0))
			return 1;
	return 0;
}

static void
insert_decl(leafnode *leaf, treenode *def, treenode *unused_container)
{
	if (leaf
	&& (leaf->hdr.tok == IDENT)
	&&  ParseStack->contxt)
	{	symentry_t *nmtbl = mk_vardecl(leaf->data.sval, def);
#define ILYA
#ifdef ILYA
		leafnode *lm = leftmost(def);
		if (lm
		&& (lm->hdr.tok != STATIC)	/* not file static */
		&& ParseStack->contxt->syms->clevel == FILE_SCOPE)
		{	leaf->syment = symtab_insert_at(ParseStack->contxt->syms, nmtbl, EXTERN_SCOPE);
			if (Verbose&2)
			printf("%s: line %d lifting %s to extern scope\n",
				progname, leaf->hdr.line,
				nmestr(leaf->data.sval));
		} else
#endif	  
		leaf->syment = symtab_insert(ParseStack->contxt->syms, nmtbl);

		if (is_func_proto(leaf->syment->node))	/* leaf->syment->node->hdr.type == TN_DECL */
		{	extern char *x_stmnt(treenode *);
			if (0) fprintf(stdout, "fct: %4d\t%s\t<%s>\n",
				leaf->hdr.line,
				nmestr(leaf->data.sval),
				x_stmnt(leaf->syment->node));
			record_fct_name(nmestr(leaf->data.sval), lm?lm->hdr.tok:0, leaf->hdr.fnm);
			/* should record if its static or not */
		}
	
		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;

		if (0)
		{	extern char *x_stmnt(treenode *);
			printf("insert decl for %s - clevel %d - nes=%p, owner=%s - <%s>\n",
				nmestr(leaf->data.sval),
				ParseStack->contxt->syms->clevel,
				leaf->syment->nes,
				leaf->syment->nes && leaf->syment->nes->owner ? leaf->syment->nes->owner : "no owner",
				x_stmnt(leaf->syment->node));
	}	}
}

static int
has_star(treenode *n)
{
	if (!n || n->hdr.which == LEAF_T)
		return 0;
	if (n->hdr.type == TN_PNTR)
		return 1;
	return has_star(n->lnode) || has_star(n->rnode);
}

static int
has_suffix_ptr(treenode *n)
{
	if (!n) return 0;

	if (n->hdr.which == LEAF_T)
	{	if (n->hdr.type  == TN_IDENT
		&&  strstr(((leafnode *)n)->data.sval->str, "Ptr") != NULL)
		{	return 1;
		}
		return 0;
	}
	return has_suffix_ptr(n->rnode) || has_suffix_ptr(n->lnode);
}

int
has_upper(char *s)
{
	while (*s != '\0')
	{	if (isupper((int) *s++))
		{	return 1;
	}	}
	return 0;
}

static char *
has_char(treenode *n)
{	char *p;

	/* must have at least one uppercase character and no underscores */
	if (!n) return NULL;

	if (n->hdr.which == LEAF_T)
	{	if (n->hdr.type  == TN_IDENT
		&&  (!has_upper(((leafnode *)n)->data.sval->str)
		||   strchr(((leafnode *)n)->data.sval->str, (int) '_') != NULL))
		{	return ((leafnode *)n)->data.sval->str;
		}
		return NULL;
	}
	p = has_char(n->rnode);
	if (p)
	{	return p;
	}
	return has_char(n->lnode);
}

static void
insert_typedef(leafnode *leaf, treenode *def, treenode *unused_container)
{
	if (leaf && (leaf->hdr.tok == IDENT))
	{	if (ParseStack->contxt)
		{	symentry_t *entry        = mk_typedef(leaf->data.sval, def); 
			leaf->syment             = symtab_insert(ParseStack->contxt->syms, entry);
			leaf->syment->nes        = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;

			if (!exclude_location((treenode *) leaf))
			{	/* 4.9.3   pointer typedefs have Ptr suffix */
				int r493 = has_star(def->rnode) && !has_suffix_ptr(def->rnode);
				/* 4.9.6   type names are capitalized component words with no underscores */
				char *r496 = has_char(def->rnode);
				if (r493)
				{	location(def);
					printf("typedef with name not ending in Ptr hides pointer\n");
				}
				if (r496)
				{	location(def);
					if (strchr(r496, (int) '_'))
					printf("typedef name '%s' contains an underscore character\n", r496);
					else
					printf("typedef name '%s' has no upper-case characters\n", r496);
			}	}

			if (list_typedefs /* && !exclude_location((treenode *) leaf) */)
			{	fprintf(stderr, "%s:%d, Typedef: %s\n",
					leaf->hdr.fnm, leaf->hdr.line,
					entry->nme->str);
				if (0)
				{	extern void print_recur(treenode *, FILE *);
					printf("\n@@@@\n");
					print_recur(def, stdout);
					printf("\n++++\n");
		}	}	}
	} else if (leaf)
	{	printf("uno: %s:%d: cannot happen, insert_typedef for %s - %s\n",	/* gjh */
			leaf->hdr.fnm, leaf->hdr.line,
			name_of_node(leaf->hdr.type),
			toksym(leaf->hdr.tok,1));
	}
}

static void
insert_component(leafnode *leaf, treenode *def, treenode *container)
{
	if (leaf && (leaf->hdr.tok == IDENT))
	if (ParseStack->contxt)
	{	symentry_t *entry = mk_component(leaf->data.sval, def, container);
		leaf->syment = symtab_insert(ParseStack->contxt->syms, entry);
		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
	}
}

static void
add_params_to_symtab(treenode *funcdecl)
{
	/* Parameters are defined at prototype/function scope */
	enter_scope(ParseStack->contxt);
#ifdef ILYA
	while (funcdecl->hdr.type == TN_DECL)
		funcdecl = funcdecl->rnode;	/* e.g., fct returns ptr */

	if (funcdecl->hdr.type != TN_FUNC_DECL)
	{	if (debug)
		printf("%s: line %d, unexpected, funcdecl = %s (%s)\n",
			progname, funcdecl->hdr.line,
			name_of_node(funcdecl->hdr.type),
			((leafnode *)funcdecl)->data.sval->str);
		return;
	}
#endif
	find_params(funcdecl, insert_decl);
}

int
current_linenumber(void)
{
	if (Parse_TOS)
		return Parse_TOS->yylineno;
	return 0;
}

char *
current_filename(void)
{	static char *CurFile = (char *) 0;

	if (Parse_TOS
	&& (!CurFile
	||  strcmp(CurFile, Parse_TOS->filename) != 0))
	{	CurFile = (char *) emalloc(strlen(Parse_TOS->filename)+1);
		strcpy(CurFile, Parse_TOS->filename);
	}
	return CurFile;
}

leafnode *
mk_ident(void)	/* lts.c */
{	static int Lnr = 1;
	char Lnm[16];
	leafnode *ln;

	sprintf(Lnm, "_L_%3d", Lnr++);
	ln = (leafnode *) emalloc(sizeof(leafnode));
	ln->hdr.which = LEAF_T;
	ln->hdr.type = TN_IDENT;
	ln->hdr.tok = IDENT;
	ln->data.sval = nmelook(Lnm,0);
	ln->syment = symtab_lookup(ParseStack->contxt->labels, ln->data.sval);

	return ln;
}

leafnode *
mk_bool(char *s)	/* "true" or "false" as identifiers - lts.c */
{	leafnode *ln;

	ln = (leafnode *) emalloc(sizeof(leafnode));
	ln->hdr.which = LEAF_T;
	ln->hdr.type = TN_IDENT;
	ln->hdr.tok = IDENT;
	ln->data.sval = nmelook(s,0);
	ln->syment = symtab_lookup(ParseStack->contxt->labels, ln->data.sval);

	return ln;
}

treenode *
mk_int(int d)	/* lts.c */
{	leafnode *ln;

	ln = (leafnode *) emalloc(sizeof(leafnode));
	ln->hdr.which = LEAF_T;
	ln->hdr.type = TN_INT;
	ln->hdr.tok = INUM;
	ln->data.ival = d;

	return (treenode *) ln;
}

treenode *
mk_deflt(void)
{	leafnode *ln;

	ln = (leafnode *) emalloc(sizeof(leafnode));
	ln->hdr.which = LEAF_T;
	ln->hdr.type = TN_LABEL;
	ln->hdr.tok = DEFLT;

	return (treenode *) ln;
}
