{-# OPTIONS_GHC -w #-}
module Parser (calc, lexer) where

import Data.List.NonEmpty (NonEmpty (..), (<|))
import qualified Data.List.NonEmpty as NE

import Lexer (Token (..), lexer)
import Types (Identifier, Literal (..), Expr (..), FuncDef' (..), Stmt (..), TopLvlStmt (..), InnerObject (..), Object (..))
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 t15
	| HappyAbsSyn16 t16
	| HappyAbsSyn17 t17
	| HappyAbsSyn18 t18
	| HappyAbsSyn19 t19
	| HappyAbsSyn20 t20
	| HappyAbsSyn21 t21
	| HappyAbsSyn22 t22
	| HappyAbsSyn23 t23
	| HappyAbsSyn24 t24
	| HappyAbsSyn25 t25
	| HappyAbsSyn26 t26
	| HappyAbsSyn27 t27
	| HappyAbsSyn28 t28
	| HappyAbsSyn29 t29
	| HappyAbsSyn30 t30
	| HappyAbsSyn31 t31

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,250) ([0,0,0,0,0,0,0,0,0,0,32768,2,0,0,0,0,0,0,512,0,0,0,1,0,128,0,0,0,0,256,0,32768,0,0,0,0,0,64,0,0,32768,2,0,8,0,0,0,0,1024,0,0,0,40,0,0,0,0,0,0,0,0,0,1,0,0,0,0,32,0,0,4096,0,0,8,0,0,0,0,16,0,0,0,0,0,33152,32768,1,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,4,0,0,128,0,0,0,1024,0,8192,0,0,0,384,65511,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,16384,0,0,0,0,0,0,0,0,8,0,0,57344,23,0,0,32256,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,64,0,0,8192,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,128,0,0,0,8,0,0,0,1,0,0,2048,0,0,0,256,0,0,36,0,0,34816,0,0,0,16384,0,0,0,0,128,0,0,0,382,0,0,32768,0,0,0,2048,0,0,0,2016,0,0,6144,0,0,8192,0,0,0,128,32768,0,0,0,2016,0,0,48,0,0,0,32768,0,0,0,32256,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,126,0,0,32768,0,0,128,32768,0,0,0,0,0,32768,0,0,0,0,384,0,0,0,0,0,0,0,0,0,0,0,118,0,2048,0,8,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,576,0,0,0,0,126,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,8,0,34816,0,0,0,0,2048,0,0,0,256,0,0,1,0,0,0,0,1,0,0,0,0,0,0,128,0,32768,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,382,0,2048,0,0,0,0,0,0,0,8,0,0,32768,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,16384,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,520,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_calc","Objects","Object","InnerObject","Code","Block","TopLvlBlock","Statements","TopLvlStmts","TopLvlStmt","Statement","FuncDef","VariableDeclaration","Assignment","Expression","If","Switch","Cases","Case","Default","ForLoop","FunctionCall","ExpressionPrecComment","Arguments","Identifiers","TypeName","TypedIdentifiers","Literal","NumberLiteral","'{'","'}'","'('","')'","'->'","':='","','","':'","function","let","if","switch","case","default","for","break","continue","leave","true","false","ident","str","hex","dec","inlcomment","multicomment","object","code","%eof"]
        bit_start = st Prelude.* 60
        bit_end = (st Prelude.+ 1) Prelude.* 60
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..59]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (4) = happyGoto action_2
action_0 _ = happyReduce_1

action_1 _ = happyFail (happyExpListPerState 1)

action_2 (56) = happyShift action_4
action_2 (58) = happyShift action_5
action_2 (60) = happyAccept
action_2 (5) = happyGoto action_3
action_2 _ = happyFail (happyExpListPerState 2)

action_3 _ = happyReduce_2

action_4 (58) = happyShift action_7
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (53) = happyShift action_6
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (32) = happyShift action_9
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (53) = happyShift action_8
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (32) = happyShift action_12
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (59) = happyShift action_11
action_9 (7) = happyGoto action_10
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (56) = happyShift action_17
action_10 (58) = happyShift action_18
action_10 (6) = happyGoto action_16
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (32) = happyShift action_15
action_11 (9) = happyGoto action_14
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (59) = happyShift action_11
action_12 (7) = happyGoto action_13
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (56) = happyShift action_17
action_13 (58) = happyShift action_18
action_13 (6) = happyGoto action_23
action_13 _ = happyFail (happyExpListPerState 13)

action_14 _ = happyReduce_7

action_15 (11) = happyGoto action_22
action_15 _ = happyReduce_12

action_16 (33) = happyShift action_21
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (58) = happyShift action_20
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (53) = happyShift action_19
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (32) = happyShift action_34
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (53) = happyShift action_33
action_20 _ = happyFail (happyExpListPerState 20)

action_21 _ = happyReduce_4

action_22 (32) = happyShift action_28
action_22 (33) = happyShift action_29
action_22 (40) = happyShift action_30
action_22 (56) = happyShift action_31
action_22 (57) = happyShift action_32
action_22 (8) = happyGoto action_25
action_22 (12) = happyGoto action_26
action_22 (14) = happyGoto action_27
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (33) = happyShift action_24
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_3

action_25 _ = happyReduce_14

action_26 _ = happyReduce_13

action_27 _ = happyReduce_15

action_28 (10) = happyGoto action_38
action_28 _ = happyReduce_10

action_29 _ = happyReduce_9

action_30 (52) = happyShift action_37
action_30 _ = happyFail (happyExpListPerState 30)

action_31 _ = happyReduce_16

action_32 _ = happyReduce_17

action_33 (32) = happyShift action_36
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (59) = happyShift action_11
action_34 (7) = happyGoto action_35
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (52) = happyShift action_69
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (59) = happyShift action_11
action_36 (7) = happyGoto action_68
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (34) = happyShift action_67
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (32) = happyShift action_28
action_38 (33) = happyShift action_51
action_38 (41) = happyShift action_52
action_38 (42) = happyShift action_53
action_38 (43) = happyShift action_54
action_38 (46) = happyShift action_55
action_38 (47) = happyShift action_56
action_38 (48) = happyShift action_57
action_38 (49) = happyShift action_58
action_38 (50) = happyShift action_59
action_38 (51) = happyShift action_60
action_38 (52) = happyShift action_61
action_38 (53) = happyShift action_62
action_38 (54) = happyShift action_63
action_38 (55) = happyShift action_64
action_38 (56) = happyShift action_65
action_38 (57) = happyShift action_66
action_38 (8) = happyGoto action_39
action_38 (13) = happyGoto action_40
action_38 (15) = happyGoto action_41
action_38 (16) = happyGoto action_42
action_38 (17) = happyGoto action_43
action_38 (18) = happyGoto action_44
action_38 (19) = happyGoto action_45
action_38 (23) = happyGoto action_46
action_38 (24) = happyGoto action_47
action_38 (27) = happyGoto action_48
action_38 (30) = happyGoto action_49
action_38 (31) = happyGoto action_50
action_38 _ = happyFail (happyExpListPerState 38)

action_39 _ = happyReduce_18

action_40 _ = happyReduce_11

action_41 _ = happyReduce_19

action_42 _ = happyReduce_20

action_43 _ = happyReduce_22

action_44 _ = happyReduce_21

action_45 _ = happyReduce_23

action_46 _ = happyReduce_24

action_47 _ = happyReduce_37

action_48 (37) = happyShift action_86
action_48 (38) = happyShift action_87
action_48 _ = happyFail (happyExpListPerState 48)

action_49 _ = happyReduce_39

action_50 (39) = happyShift action_85
action_50 _ = happyReduce_66

action_51 _ = happyReduce_8

action_52 (52) = happyShift action_74
action_52 (29) = happyGoto action_84
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (50) = happyShift action_59
action_53 (51) = happyShift action_60
action_53 (52) = happyShift action_81
action_53 (53) = happyShift action_62
action_53 (54) = happyShift action_63
action_53 (55) = happyShift action_64
action_53 (57) = happyShift action_83
action_53 (17) = happyGoto action_82
action_53 (24) = happyGoto action_47
action_53 (30) = happyGoto action_49
action_53 (31) = happyGoto action_50
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (50) = happyShift action_59
action_54 (51) = happyShift action_60
action_54 (52) = happyShift action_81
action_54 (53) = happyShift action_62
action_54 (54) = happyShift action_63
action_54 (55) = happyShift action_64
action_54 (17) = happyGoto action_80
action_54 (24) = happyGoto action_47
action_54 (30) = happyGoto action_49
action_54 (31) = happyGoto action_50
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (32) = happyShift action_28
action_55 (8) = happyGoto action_79
action_55 _ = happyFail (happyExpListPerState 55)

action_56 _ = happyReduce_26

action_57 _ = happyReduce_25

action_58 _ = happyReduce_27

action_59 (39) = happyShift action_78
action_59 _ = happyReduce_70

action_60 (39) = happyShift action_77
action_60 _ = happyReduce_72

action_61 (34) = happyShift action_76
action_61 (37) = happyReduce_59
action_61 (38) = happyReduce_59
action_61 _ = happyReduce_38

action_62 (39) = happyShift action_75
action_62 _ = happyReduce_68

action_63 _ = happyReduce_74

action_64 _ = happyReduce_75

action_65 _ = happyReduce_28

action_66 _ = happyReduce_29

action_67 (35) = happyShift action_73
action_67 (52) = happyShift action_74
action_67 (29) = happyGoto action_72
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (52) = happyShift action_71
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (53) = happyShift action_70
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (52) = happyShift action_115
action_70 _ = happyFail (happyExpListPerState 70)

action_71 (53) = happyShift action_114
action_71 _ = happyFail (happyExpListPerState 71)

action_72 (35) = happyShift action_113
action_72 (38) = happyShift action_93
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (32) = happyShift action_28
action_73 (36) = happyShift action_112
action_73 (8) = happyGoto action_111
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (39) = happyShift action_110
action_74 _ = happyReduce_62

action_75 (52) = happyShift action_91
action_75 (28) = happyGoto action_109
action_75 _ = happyFail (happyExpListPerState 75)

action_76 (50) = happyShift action_59
action_76 (51) = happyShift action_60
action_76 (52) = happyShift action_81
action_76 (53) = happyShift action_62
action_76 (54) = happyShift action_63
action_76 (55) = happyShift action_64
action_76 (57) = happyShift action_108
action_76 (17) = happyGoto action_105
action_76 (24) = happyGoto action_47
action_76 (25) = happyGoto action_106
action_76 (26) = happyGoto action_107
action_76 (30) = happyGoto action_49
action_76 (31) = happyGoto action_50
action_76 _ = happyReduce_56

action_77 (52) = happyShift action_91
action_77 (28) = happyGoto action_104
action_77 _ = happyFail (happyExpListPerState 77)

action_78 (52) = happyShift action_91
action_78 (28) = happyGoto action_103
action_78 _ = happyFail (happyExpListPerState 78)

action_79 (50) = happyShift action_59
action_79 (51) = happyShift action_60
action_79 (52) = happyShift action_81
action_79 (53) = happyShift action_62
action_79 (54) = happyShift action_63
action_79 (55) = happyShift action_64
action_79 (17) = happyGoto action_102
action_79 (24) = happyGoto action_47
action_79 (30) = happyGoto action_49
action_79 (31) = happyGoto action_50
action_79 _ = happyFail (happyExpListPerState 79)

action_80 (44) = happyShift action_100
action_80 (45) = happyShift action_101
action_80 (20) = happyGoto action_97
action_80 (21) = happyGoto action_98
action_80 (22) = happyGoto action_99
action_80 _ = happyFail (happyExpListPerState 80)

action_81 (34) = happyShift action_76
action_81 _ = happyReduce_38

action_82 (32) = happyShift action_28
action_82 (56) = happyShift action_96
action_82 (8) = happyGoto action_95
action_82 _ = happyFail (happyExpListPerState 82)

action_83 (50) = happyShift action_59
action_83 (51) = happyShift action_60
action_83 (52) = happyShift action_81
action_83 (53) = happyShift action_62
action_83 (54) = happyShift action_63
action_83 (55) = happyShift action_64
action_83 (17) = happyGoto action_94
action_83 (24) = happyGoto action_47
action_83 (30) = happyGoto action_49
action_83 (31) = happyGoto action_50
action_83 _ = happyFail (happyExpListPerState 83)

action_84 (37) = happyShift action_92
action_84 (38) = happyShift action_93
action_84 _ = happyReduce_34

action_85 (52) = happyShift action_91
action_85 (28) = happyGoto action_90
action_85 _ = happyFail (happyExpListPerState 85)

action_86 (50) = happyShift action_59
action_86 (51) = happyShift action_60
action_86 (52) = happyShift action_81
action_86 (53) = happyShift action_62
action_86 (54) = happyShift action_63
action_86 (55) = happyShift action_64
action_86 (17) = happyGoto action_89
action_86 (24) = happyGoto action_47
action_86 (30) = happyGoto action_49
action_86 (31) = happyGoto action_50
action_86 _ = happyFail (happyExpListPerState 86)

action_87 (52) = happyShift action_88
action_87 _ = happyFail (happyExpListPerState 87)

action_88 _ = happyReduce_60

action_89 _ = happyReduce_36

action_90 _ = happyReduce_67

action_91 _ = happyReduce_61

action_92 (50) = happyShift action_59
action_92 (51) = happyShift action_60
action_92 (52) = happyShift action_81
action_92 (53) = happyShift action_62
action_92 (54) = happyShift action_63
action_92 (55) = happyShift action_64
action_92 (17) = happyGoto action_135
action_92 (24) = happyGoto action_47
action_92 (30) = happyGoto action_49
action_92 (31) = happyGoto action_50
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (52) = happyShift action_134
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (32) = happyShift action_28
action_94 (56) = happyShift action_133
action_94 (8) = happyGoto action_132
action_94 _ = happyFail (happyExpListPerState 94)

action_95 _ = happyReduce_40

action_96 (32) = happyShift action_28
action_96 (8) = happyGoto action_131
action_96 _ = happyFail (happyExpListPerState 96)

action_97 (44) = happyShift action_100
action_97 (45) = happyShift action_101
action_97 (21) = happyGoto action_129
action_97 (22) = happyGoto action_130
action_97 _ = happyReduce_44

action_98 _ = happyReduce_47

action_99 _ = happyReduce_46

action_100 (50) = happyShift action_59
action_100 (51) = happyShift action_60
action_100 (53) = happyShift action_62
action_100 (54) = happyShift action_63
action_100 (55) = happyShift action_64
action_100 (30) = happyGoto action_128
action_100 (31) = happyGoto action_50
action_100 _ = happyFail (happyExpListPerState 100)

action_101 (32) = happyShift action_28
action_101 (56) = happyShift action_127
action_101 (8) = happyGoto action_126
action_101 _ = happyFail (happyExpListPerState 101)

action_102 (32) = happyShift action_28
action_102 (8) = happyGoto action_125
action_102 _ = happyFail (happyExpListPerState 102)

action_103 _ = happyReduce_71

action_104 _ = happyReduce_73

action_105 _ = happyReduce_55

action_106 _ = happyReduce_57

action_107 (35) = happyShift action_123
action_107 (38) = happyShift action_124
action_107 _ = happyFail (happyExpListPerState 107)

action_108 (50) = happyShift action_59
action_108 (51) = happyShift action_60
action_108 (52) = happyShift action_81
action_108 (53) = happyShift action_62
action_108 (54) = happyShift action_63
action_108 (55) = happyShift action_64
action_108 (17) = happyGoto action_122
action_108 (24) = happyGoto action_47
action_108 (30) = happyGoto action_49
action_108 (31) = happyGoto action_50
action_108 _ = happyFail (happyExpListPerState 108)

action_109 _ = happyReduce_69

action_110 (52) = happyShift action_91
action_110 (28) = happyGoto action_121
action_110 _ = happyFail (happyExpListPerState 110)

action_111 _ = happyReduce_30

action_112 (52) = happyShift action_74
action_112 (29) = happyGoto action_120
action_112 _ = happyFail (happyExpListPerState 112)

action_113 (32) = happyShift action_28
action_113 (36) = happyShift action_119
action_113 (8) = happyGoto action_118
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (52) = happyShift action_117
action_114 _ = happyFail (happyExpListPerState 114)

action_115 (53) = happyShift action_116
action_115 _ = happyFail (happyExpListPerState 115)

action_116 (33) = happyShift action_145
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (53) = happyShift action_144
action_117 _ = happyFail (happyExpListPerState 117)

action_118 _ = happyReduce_31

action_119 (52) = happyShift action_74
action_119 (29) = happyGoto action_143
action_119 _ = happyFail (happyExpListPerState 119)

action_120 (32) = happyShift action_28
action_120 (38) = happyShift action_93
action_120 (8) = happyGoto action_142
action_120 _ = happyFail (happyExpListPerState 120)

action_121 _ = happyReduce_63

action_122 _ = happyReduce_54

action_123 _ = happyReduce_53

action_124 (50) = happyShift action_59
action_124 (51) = happyShift action_60
action_124 (52) = happyShift action_81
action_124 (53) = happyShift action_62
action_124 (54) = happyShift action_63
action_124 (55) = happyShift action_64
action_124 (57) = happyShift action_108
action_124 (17) = happyGoto action_105
action_124 (24) = happyGoto action_47
action_124 (25) = happyGoto action_141
action_124 (30) = happyGoto action_49
action_124 (31) = happyGoto action_50
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (32) = happyShift action_28
action_125 (8) = happyGoto action_140
action_125 _ = happyFail (happyExpListPerState 125)

action_126 _ = happyReduce_50

action_127 (32) = happyShift action_28
action_127 (8) = happyGoto action_139
action_127 _ = happyFail (happyExpListPerState 127)

action_128 (32) = happyShift action_28
action_128 (8) = happyGoto action_138
action_128 _ = happyFail (happyExpListPerState 128)

action_129 _ = happyReduce_48

action_130 _ = happyReduce_45

action_131 _ = happyReduce_42

action_132 _ = happyReduce_41

action_133 (32) = happyShift action_28
action_133 (8) = happyGoto action_137
action_133 _ = happyFail (happyExpListPerState 133)

action_134 (39) = happyShift action_136
action_134 _ = happyReduce_64

action_135 _ = happyReduce_35

action_136 (52) = happyShift action_91
action_136 (28) = happyGoto action_148
action_136 _ = happyFail (happyExpListPerState 136)

action_137 _ = happyReduce_43

action_138 _ = happyReduce_49

action_139 _ = happyReduce_51

action_140 _ = happyReduce_52

action_141 _ = happyReduce_58

action_142 _ = happyReduce_32

action_143 (32) = happyShift action_28
action_143 (38) = happyShift action_93
action_143 (8) = happyGoto action_147
action_143 _ = happyFail (happyExpListPerState 143)

action_144 (33) = happyShift action_146
action_144 _ = happyFail (happyExpListPerState 144)

action_145 _ = happyReduce_6

action_146 _ = happyReduce_5

action_147 _ = happyReduce_33

action_148 _ = happyReduce_65

happyReduce_1 = happySpecReduce_0  4 happyReduction_1
happyReduction_1  =  HappyAbsSyn4
		 ([]
	)

happyReduce_2 = happySpecReduce_2  4 happyReduction_2
happyReduction_2 (HappyAbsSyn5  happy_var_2)
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_2 : happy_var_1
	)
happyReduction_2 _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 7 5 happyReduction_3
happyReduction_3 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_6) `HappyStk`
	(HappyAbsSyn7  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenString happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenInlineComment happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Object happy_var_1 happy_var_3 happy_var_5 happy_var_6
	) `HappyStk` happyRest

happyReduce_4 = happyReduce 6 5 happyReduction_4
happyReduction_4 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenString happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Object "" happy_var_2 happy_var_4 happy_var_5
	) `HappyStk` happyRest

happyReduce_5 = happyReduce 10 6 happyReduction_5
happyReduction_5 (_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenString happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenInlineComment happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (InnerObject happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_6 = happyReduce 9 6 happyReduction_6
happyReduction_6 (_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenString happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (InnerObject "" happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_2  7 happyReduction_7
happyReduction_7 (HappyAbsSyn9  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (happy_var_2
	)
happyReduction_7 _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_3  8 happyReduction_8
happyReduction_8 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (reverse happy_var_2
	)
happyReduction_8 _ _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  9 happyReduction_9
happyReduction_9 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (reverse happy_var_2
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_0  10 happyReduction_10
happyReduction_10  =  HappyAbsSyn10
		 ([]
	)

happyReduce_11 = happySpecReduce_2  10 happyReduction_11
happyReduction_11 (HappyAbsSyn13  happy_var_2)
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_2 : happy_var_1
	)
happyReduction_11 _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_0  11 happyReduction_12
happyReduction_12  =  HappyAbsSyn11
		 ([]
	)

happyReduce_13 = happySpecReduce_2  11 happyReduction_13
happyReduction_13 (HappyAbsSyn12  happy_var_2)
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_2 : happy_var_1
	)
happyReduction_13 _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  12 happyReduction_14
happyReduction_14 _
	 =  HappyAbsSyn12
		 (UnusedBlock
	)

happyReduce_15 = happySpecReduce_1  12 happyReduction_15
happyReduction_15 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn12
		 (FuncDefStmt happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  12 happyReduction_16
happyReduction_16 _
	 =  HappyAbsSyn12
		 (UnusedBlock
	)

happyReduce_17 = happySpecReduce_1  12 happyReduction_17
happyReduction_17 _
	 =  HappyAbsSyn12
		 (UnusedBlock
	)

happyReduce_18 = happySpecReduce_1  13 happyReduction_18
happyReduction_18 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn13
		 (Block happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  13 happyReduction_19
happyReduction_19 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn13
		 (let (idens, mbExpr) = happy_var_1 in
                                                case mbExpr of
                                                  Just expr -> LetInit idens expr
                                                  Nothing   -> Declaration idens
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  13 happyReduction_20
happyReduction_20 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn13
		 ((uncurry Assignment) happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  13 happyReduction_21
happyReduction_21 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn13
		 ((uncurry If) happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  13 happyReduction_22
happyReduction_22 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn13
		 (ExpressionStmt happy_var_1
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  13 happyReduction_23
happyReduction_23 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn13
		 ((uncurry3 Switch) happy_var_1
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  13 happyReduction_24
happyReduction_24 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn13
		 ((uncurry4 For) happy_var_1
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  13 happyReduction_25
happyReduction_25 _
	 =  HappyAbsSyn13
		 (Continue
	)

happyReduce_26 = happySpecReduce_1  13 happyReduction_26
happyReduction_26 _
	 =  HappyAbsSyn13
		 (Break
	)

happyReduce_27 = happySpecReduce_1  13 happyReduction_27
happyReduction_27 _
	 =  HappyAbsSyn13
		 (Leave
	)

happyReduce_28 = happySpecReduce_1  13 happyReduction_28
happyReduction_28 (HappyTerminal (TokenInlineComment happy_var_1))
	 =  HappyAbsSyn13
		 (InlineComment happy_var_1
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  13 happyReduction_29
happyReduction_29 (HappyTerminal (TokenMultilineComment happy_var_1))
	 =  HappyAbsSyn13
		 (MultilineComment happy_var_1
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happyReduce 5 14 happyReduction_30
happyReduction_30 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (FuncDef' happy_var_2 [] [] happy_var_5
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 6 14 happyReduction_31
happyReduction_31 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (FuncDef' happy_var_2 (reverse (NE.toList happy_var_4)) [] happy_var_6
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 7 14 happyReduction_32
happyReduction_32 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	(HappyAbsSyn29  happy_var_6) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (FuncDef' happy_var_2 [] (reverse (NE.toList happy_var_6)) happy_var_7
	) `HappyStk` happyRest

happyReduce_33 = happyReduce 8 14 happyReduction_33
happyReduction_33 ((HappyAbsSyn8  happy_var_8) `HappyStk`
	(HappyAbsSyn29  happy_var_7) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (FuncDef' happy_var_2 (reverse (NE.toList happy_var_4)) (reverse (NE.toList happy_var_7)) happy_var_8
	) `HappyStk` happyRest

happyReduce_34 = happySpecReduce_2  15 happyReduction_34
happyReduction_34 (HappyAbsSyn29  happy_var_2)
	_
	 =  HappyAbsSyn15
		 ((NE.reverse happy_var_2, Nothing)
	)
happyReduction_34 _ _  = notHappyAtAll 

happyReduce_35 = happyReduce 4 15 happyReduction_35
happyReduction_35 ((HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((NE.reverse happy_var_2, Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_36 = happySpecReduce_3  16 happyReduction_36
happyReduction_36 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn16
		 ((NE.reverse happy_var_1, happy_var_3)
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_1  17 happyReduction_37
happyReduction_37 (HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn17
		 ((uncurry Call) happy_var_1
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_1  17 happyReduction_38
happyReduction_38 (HappyTerminal (TokenIdentifier happy_var_1))
	 =  HappyAbsSyn17
		 (Var happy_var_1
	)
happyReduction_38 _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_1  17 happyReduction_39
happyReduction_39 (HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn17
		 (Lit happy_var_1
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  18 happyReduction_40
happyReduction_40 (HappyAbsSyn8  happy_var_3)
	(HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn18
		 ((happy_var_2, happy_var_3)
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happyReduce 4 18 happyReduction_41
happyReduction_41 ((HappyAbsSyn8  happy_var_4) `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 ((happy_var_3, happy_var_4)
	) `HappyStk` happyRest

happyReduce_42 = happyReduce 4 18 happyReduction_42
happyReduction_42 ((HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 ((happy_var_2, happy_var_4)
	) `HappyStk` happyRest

happyReduce_43 = happyReduce 5 18 happyReduction_43
happyReduction_43 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 ((happy_var_3, happy_var_5)
	) `HappyStk` happyRest

happyReduce_44 = happySpecReduce_3  19 happyReduction_44
happyReduction_44 (HappyAbsSyn20  happy_var_3)
	(HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn19
		 ((happy_var_2, reverse happy_var_3, [])
	)
happyReduction_44 _ _ _  = notHappyAtAll 

happyReduce_45 = happyReduce 4 19 happyReduction_45
happyReduction_45 ((HappyAbsSyn22  happy_var_4) `HappyStk`
	(HappyAbsSyn20  happy_var_3) `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 ((happy_var_2, reverse happy_var_3, happy_var_4)
	) `HappyStk` happyRest

happyReduce_46 = happySpecReduce_3  19 happyReduction_46
happyReduction_46 (HappyAbsSyn22  happy_var_3)
	(HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn19
		 ((happy_var_2, [],         happy_var_3)
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  20 happyReduction_47
happyReduction_47 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn20
		 ([happy_var_1]
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_2  20 happyReduction_48
happyReduction_48 (HappyAbsSyn21  happy_var_2)
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_2 : happy_var_1
	)
happyReduction_48 _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_3  21 happyReduction_49
happyReduction_49 (HappyAbsSyn8  happy_var_3)
	(HappyAbsSyn30  happy_var_2)
	_
	 =  HappyAbsSyn21
		 ((happy_var_2, happy_var_3)
	)
happyReduction_49 _ _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_2  22 happyReduction_50
happyReduction_50 (HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn22
		 (happy_var_2
	)
happyReduction_50 _ _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_3  22 happyReduction_51
happyReduction_51 (HappyAbsSyn8  happy_var_3)
	_
	_
	 =  HappyAbsSyn22
		 (happy_var_3
	)
happyReduction_51 _ _ _  = notHappyAtAll 

happyReduce_52 = happyReduce 5 23 happyReduction_52
happyReduction_52 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((happy_var_2, happy_var_3, happy_var_4, happy_var_5)
	) `HappyStk` happyRest

happyReduce_53 = happyReduce 4 24 happyReduction_53
happyReduction_53 (_ `HappyStk`
	(HappyAbsSyn26  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn24
		 ((happy_var_1, reverse happy_var_3)
	) `HappyStk` happyRest

happyReduce_54 = happySpecReduce_2  25 happyReduction_54
happyReduction_54 (HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn25
		 (happy_var_2
	)
happyReduction_54 _ _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_1  25 happyReduction_55
happyReduction_55 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn25
		 (happy_var_1
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_0  26 happyReduction_56
happyReduction_56  =  HappyAbsSyn26
		 ([]
	)

happyReduce_57 = happySpecReduce_1  26 happyReduction_57
happyReduction_57 (HappyAbsSyn25  happy_var_1)
	 =  HappyAbsSyn26
		 ([happy_var_1]
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_3  26 happyReduction_58
happyReduction_58 (HappyAbsSyn25  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_3 : happy_var_1
	)
happyReduction_58 _ _ _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_1  27 happyReduction_59
happyReduction_59 (HappyTerminal (TokenIdentifier happy_var_1))
	 =  HappyAbsSyn27
		 (happy_var_1 :| []
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_3  27 happyReduction_60
happyReduction_60 (HappyTerminal (TokenIdentifier happy_var_3))
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn27
		 (happy_var_3 <| happy_var_1
	)
happyReduction_60 _ _ _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_1  28 happyReduction_61
happyReduction_61 (HappyTerminal (TokenIdentifier happy_var_1))
	 =  HappyAbsSyn28
		 (happy_var_1
	)
happyReduction_61 _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_1  29 happyReduction_62
happyReduction_62 (HappyTerminal (TokenIdentifier happy_var_1))
	 =  HappyAbsSyn29
		 (happy_var_1 :| []
	)
happyReduction_62 _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_3  29 happyReduction_63
happyReduction_63 _
	_
	(HappyTerminal (TokenIdentifier happy_var_1))
	 =  HappyAbsSyn29
		 (happy_var_1 :| []
	)
happyReduction_63 _ _ _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_3  29 happyReduction_64
happyReduction_64 (HappyTerminal (TokenIdentifier happy_var_3))
	_
	(HappyAbsSyn29  happy_var_1)
	 =  HappyAbsSyn29
		 (happy_var_3 <| happy_var_1
	)
happyReduction_64 _ _ _  = notHappyAtAll 

happyReduce_65 = happyReduce 5 29 happyReduction_65
happyReduction_65 (_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenIdentifier happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn29
		 (happy_var_3 <| happy_var_1
	) `HappyStk` happyRest

happyReduce_66 = happySpecReduce_1  30 happyReduction_66
happyReduction_66 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn30
		 (Number happy_var_1
	)
happyReduction_66 _  = notHappyAtAll 

happyReduce_67 = happySpecReduce_3  30 happyReduction_67
happyReduction_67 _
	_
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn30
		 (Number happy_var_1
	)
happyReduction_67 _ _ _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_1  30 happyReduction_68
happyReduction_68 (HappyTerminal (TokenString happy_var_1))
	 =  HappyAbsSyn30
		 (Str happy_var_1
	)
happyReduction_68 _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_3  30 happyReduction_69
happyReduction_69 _
	_
	(HappyTerminal (TokenString happy_var_1))
	 =  HappyAbsSyn30
		 (Str happy_var_1
	)
happyReduction_69 _ _ _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_1  30 happyReduction_70
happyReduction_70 _
	 =  HappyAbsSyn30
		 (Number 1
	)

happyReduce_71 = happySpecReduce_3  30 happyReduction_71
happyReduction_71 _
	_
	_
	 =  HappyAbsSyn30
		 (Number 1
	)

happyReduce_72 = happySpecReduce_1  30 happyReduction_72
happyReduction_72 _
	 =  HappyAbsSyn30
		 (Number 0
	)

happyReduce_73 = happySpecReduce_3  30 happyReduction_73
happyReduction_73 _
	_
	_
	 =  HappyAbsSyn30
		 (Number 0
	)

happyReduce_74 = happySpecReduce_1  31 happyReduction_74
happyReduction_74 (HappyTerminal (TokenHex happy_var_1))
	 =  HappyAbsSyn31
		 ((read happy_var_1)
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_1  31 happyReduction_75
happyReduction_75 (HappyTerminal (TokenDecimal happy_var_1))
	 =  HappyAbsSyn31
		 ((read happy_var_1)
	)
happyReduction_75 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 60 60 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenLCurl -> cont 32;
	TokenRCurl -> cont 33;
	TokenLPar -> cont 34;
	TokenRPar -> cont 35;
	TokenArrow -> cont 36;
	TokenColonEq -> cont 37;
	TokenComma -> cont 38;
	TokenColon -> cont 39;
	TokenFunction -> cont 40;
	TokenLet -> cont 41;
	TokenIf -> cont 42;
	TokenSwitch -> cont 43;
	TokenCase -> cont 44;
	TokenDefault -> cont 45;
	TokenFor -> cont 46;
	TokenBreak -> cont 47;
	TokenContinue -> cont 48;
	TokenLeave -> cont 49;
	TokenTrue -> cont 50;
	TokenFalse -> cont 51;
	TokenIdentifier happy_dollar_dollar -> cont 52;
	TokenString happy_dollar_dollar -> cont 53;
	TokenHex happy_dollar_dollar -> cont 54;
	TokenDecimal happy_dollar_dollar -> cont 55;
	TokenInlineComment happy_dollar_dollar -> cont 56;
	TokenMultilineComment happy_dollar_dollar -> cont 57;
	TokenObject -> cont 58;
	TokenCode -> cont 59;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 60 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Prelude.Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Prelude.Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (Prelude.return)
happyThen1 m k tks = (Prelude.>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (Prelude.return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> HappyIdentity a
happyError' = HappyIdentity Prelude.. (\(tokens, _) -> parseError tokens)
calc tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError ts = error ("Can't parse tokens: " ++ show (take 10 ts))

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

uncurry4 :: (a -> b -> c -> d -> e) -> (a, b, c, d) -> e
uncurry4 f (w, x, y, z) = f w x y z
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
