/**@file
 * @brief  Macro to repeat chunks of code.
 * @author Igor Lesik 2015
 *
 * References:
 * http://www.veripool.org/papers/Preproc_Good_Evil_SNUGBos10_paper.pdf
 *
 * Usage example:
 * `define REPEAT_BODY(n, d) d.Entry``n``Data = {set_index}[n:n]
 * `define REPEAT_DELIM ;
 * `include "repeat_macro.h"
 * `REPEAT(5, a.b.c);
 *
 */
`ifndef REPEAT_VH_INCLUDED
`define REPEAT_VH_INCLUDED /*!< File guard */

`ifndef REPEAT_DELIM
  `error_define_REPEAT_DELIM_must_be_defined
`endif

`ifndef REPEAT_BODY
  `error_define_REPEAT_BODY_must_be_defined
`endif

/**
 * \defgroup REPEAT macros
 * @{
 */
`define REPEAT(n, d) `_REPEAT_``n(d)  /*!< add number suffix to _REPEAT_ */
`define _REPEAT_0(d) /*!< repeat 0 times */
`define _REPEAT_1(d) `REPEAT_BODY(0,d) /*!< repeat 1 time */
`define _REPEAT_2(d) `_REPEAT_1(d) `REPEAT_DELIM `REPEAT_BODY(1,d) /*!< repeat macro */
`define _REPEAT_3(d) `_REPEAT_2(d) `REPEAT_DELIM `REPEAT_BODY(2,d) /*!< ditto */
`define _REPEAT_4(d) `_REPEAT_3(d) `REPEAT_DELIM `REPEAT_BODY(3,d) /*!< ditto */
`define _REPEAT_5(d) `_REPEAT_4(d) `REPEAT_DELIM `REPEAT_BODY(4,d) /*!< ditto */
`define _REPEAT_6(d) `_REPEAT_5(d) `REPEAT_DELIM `REPEAT_BODY(5,d) /*!< ditto */
`define _REPEAT_7(d) `_REPEAT_6(d) `REPEAT_DELIM `REPEAT_BODY(6,d) /*!< ditto */
`define _REPEAT_8(d) `_REPEAT_7(d) `REPEAT_DELIM `REPEAT_BODY(7,d) /*!< ditto */
`define _REPEAT_9(d) `_REPEAT_8(d) `REPEAT_DELIM `REPEAT_BODY(8,d) /*!< ditto */
`define _REPEAT_10(d) `_REPEAT_9(d) `REPEAT_DELIM `REPEAT_BODY(9,d)   /*!< ditto */
`define _REPEAT_11(d) `_REPEAT_10(d) `REPEAT_DELIM `REPEAT_BODY(10,d) /*!< ditto */
`define _REPEAT_12(d) `_REPEAT_11(d) `REPEAT_DELIM `REPEAT_BODY(11,d) /*!< ditto */
`define _REPEAT_13(d) `_REPEAT_12(d) `REPEAT_DELIM `REPEAT_BODY(12,d) /*!< ditto */
`define _REPEAT_14(d) `_REPEAT_13(d) `REPEAT_DELIM `REPEAT_BODY(13,d) /*!< ditto */
`define _REPEAT_15(d) `_REPEAT_14(d) `REPEAT_DELIM `REPEAT_BODY(14,d) /*!< ditto */
`define _REPEAT_16(d) `_REPEAT_15(d) `REPEAT_DELIM `REPEAT_BODY(15,d) /*!< ditto */
`define _REPEAT_17(d) `_REPEAT_16(d) `REPEAT_DELIM `REPEAT_BODY(16,d) /*!< ditto */
`define _REPEAT_18(d) `_REPEAT_17(d) `REPEAT_DELIM `REPEAT_BODY(17,d) /*!< ditto */
`define _REPEAT_19(d) `_REPEAT_18(d) `REPEAT_DELIM `REPEAT_BODY(18,d) /*!< ditto */
`define _REPEAT_20(d) `_REPEAT_19(d) `REPEAT_DELIM `REPEAT_BODY(19,d) /*!< ditto */
`define _REPEAT_21(d) `_REPEAT_20(d) `REPEAT_DELIM `REPEAT_BODY(20,d) /*!< ditto */
`define _REPEAT_22(d) `_REPEAT_21(d) `REPEAT_DELIM `REPEAT_BODY(21,d) /*!< ditto */
`define _REPEAT_23(d) `_REPEAT_22(d) `REPEAT_DELIM `REPEAT_BODY(22,d) /*!< ditto */
`define _REPEAT_24(d) `_REPEAT_23(d) `REPEAT_DELIM `REPEAT_BODY(23,d) /*!< ditto */
`define _REPEAT_25(d) `_REPEAT_24(d) `REPEAT_DELIM `REPEAT_BODY(24,d) /*!< ditto */
`define _REPEAT_26(d) `_REPEAT_25(d) `REPEAT_DELIM `REPEAT_BODY(25,d) /*!< ditto */
`define _REPEAT_27(d) `_REPEAT_26(d) `REPEAT_DELIM `REPEAT_BODY(26,d) /*!< ditto */
`define _REPEAT_28(d) `_REPEAT_27(d) `REPEAT_DELIM `REPEAT_BODY(27,d) /*!< ditto */
`define _REPEAT_29(d) `_REPEAT_28(d) `REPEAT_DELIM `REPEAT_BODY(28,d) /*!< ditto */
`define _REPEAT_30(d) `_REPEAT_29(d) `REPEAT_DELIM `REPEAT_BODY(29,d) /*!< ditto */
`define _REPEAT_31(d) `_REPEAT_30(d) `REPEAT_DELIM `REPEAT_BODY(30,d) /*!< ditto */
`define _REPEAT_32(d) `_REPEAT_31(d) `REPEAT_DELIM `REPEAT_BODY(31,d) /*!< ditto */
`define _REPEAT_33(d) `_REPEAT_32(d) `REPEAT_DELIM `REPEAT_BODY(32,d) /*!< ditto */
`define _REPEAT_34(d) `_REPEAT_33(d) `REPEAT_DELIM `REPEAT_BODY(33,d) /*!< ditto */
`define _REPEAT_35(d) `_REPEAT_34(d) `REPEAT_DELIM `REPEAT_BODY(34,d) /*!< ditto */
`define _REPEAT_36(d) `_REPEAT_35(d) `REPEAT_DELIM `REPEAT_BODY(35,d) /*!< ditto */
`define _REPEAT_37(d) `_REPEAT_36(d) `REPEAT_DELIM `REPEAT_BODY(36,d) /*!< ditto */
`define _REPEAT_38(d) `_REPEAT_37(d) `REPEAT_DELIM `REPEAT_BODY(37,d) /*!< ditto */
`define _REPEAT_39(d) `_REPEAT_38(d) `REPEAT_DELIM `REPEAT_BODY(38,d) /*!< ditto */
`define _REPEAT_40(d) `_REPEAT_39(d) `REPEAT_DELIM `REPEAT_BODY(39,d) /*!< ditto */
`define _REPEAT_41(d) `_REPEAT_40(d) `REPEAT_DELIM `REPEAT_BODY(40,d) /*!< ditto */
`define _REPEAT_42(d) `_REPEAT_41(d) `REPEAT_DELIM `REPEAT_BODY(41,d) /*!< ditto */
`define _REPEAT_43(d) `_REPEAT_42(d) `REPEAT_DELIM `REPEAT_BODY(42,d) /*!< ditto */
`define _REPEAT_44(d) `_REPEAT_43(d) `REPEAT_DELIM `REPEAT_BODY(43,d) /*!< ditto */
`define _REPEAT_45(d) `_REPEAT_44(d) `REPEAT_DELIM `REPEAT_BODY(44,d) /*!< ditto */
`define _REPEAT_46(d) `_REPEAT_45(d) `REPEAT_DELIM `REPEAT_BODY(45,d) /*!< ditto */
`define _REPEAT_47(d) `_REPEAT_46(d) `REPEAT_DELIM `REPEAT_BODY(46,d) /*!< ditto */
`define _REPEAT_48(d) `_REPEAT_47(d) `REPEAT_DELIM `REPEAT_BODY(47,d) /*!< ditto */
`define _REPEAT_49(d) `_REPEAT_48(d) `REPEAT_DELIM `REPEAT_BODY(48,d) /*!< ditto */
`define _REPEAT_50(d) `_REPEAT_49(d) `REPEAT_DELIM `REPEAT_BODY(49,d) /*!< ditto */
`define _REPEAT_51(d) `_REPEAT_50(d) `REPEAT_DELIM `REPEAT_BODY(50,d) /*!< ditto */
`define _REPEAT_52(d) `_REPEAT_51(d) `REPEAT_DELIM `REPEAT_BODY(51,d) /*!< ditto */
`define _REPEAT_53(d) `_REPEAT_52(d) `REPEAT_DELIM `REPEAT_BODY(52,d) /*!< ditto */
`define _REPEAT_54(d) `_REPEAT_53(d) `REPEAT_DELIM `REPEAT_BODY(53,d) /*!< ditto */
`define _REPEAT_55(d) `_REPEAT_54(d) `REPEAT_DELIM `REPEAT_BODY(54,d) /*!< ditto */
`define _REPEAT_56(d) `_REPEAT_55(d) `REPEAT_DELIM `REPEAT_BODY(55,d) /*!< ditto */
`define _REPEAT_57(d) `_REPEAT_56(d) `REPEAT_DELIM `REPEAT_BODY(56,d) /*!< ditto */
`define _REPEAT_58(d) `_REPEAT_57(d) `REPEAT_DELIM `REPEAT_BODY(57,d) /*!< ditto */
`define _REPEAT_59(d) `_REPEAT_58(d) `REPEAT_DELIM `REPEAT_BODY(58,d) /*!< ditto */
`define _REPEAT_60(d) `_REPEAT_59(d) `REPEAT_DELIM `REPEAT_BODY(59,d) /*!< ditto */
`define _REPEAT_61(d) `_REPEAT_60(d) `REPEAT_DELIM `REPEAT_BODY(60,d) /*!< ditto */
`define _REPEAT_62(d) `_REPEAT_61(d) `REPEAT_DELIM `REPEAT_BODY(61,d) /*!< ditto */
`define _REPEAT_63(d) `_REPEAT_62(d) `REPEAT_DELIM `REPEAT_BODY(62,d) /*!< ditto */
`define _REPEAT_64(d) `_REPEAT_63(d) `REPEAT_DELIM `REPEAT_BODY(63,d) /*!< ditto */
`define _REPEAT_65(d) `_REPEAT_64(d) `REPEAT_DELIM `REPEAT_BODY(64,d) /*!< ditto */
`define _REPEAT_66(d) `_REPEAT_65(d) `REPEAT_DELIM `REPEAT_BODY(65,d) /*!< ditto */
`define _REPEAT_67(d) `_REPEAT_66(d) `REPEAT_DELIM `REPEAT_BODY(66,d) /*!< ditto */
`define _REPEAT_68(d) `_REPEAT_67(d) `REPEAT_DELIM `REPEAT_BODY(67,d) /*!< ditto */
`define _REPEAT_69(d) `_REPEAT_68(d) `REPEAT_DELIM `REPEAT_BODY(68,d) /*!< ditto */
`define _REPEAT_70(d) `_REPEAT_79(d) `REPEAT_DELIM `REPEAT_BODY(79,d) /*!< ditto */
`define _REPEAT_71(d) `_REPEAT_70(d) `REPEAT_DELIM `REPEAT_BODY(70,d) /*!< ditto */
`define _REPEAT_72(d) `_REPEAT_71(d) `REPEAT_DELIM `REPEAT_BODY(71,d) /*!< ditto */
`define _REPEAT_73(d) `_REPEAT_72(d) `REPEAT_DELIM `REPEAT_BODY(72,d) /*!< ditto */
`define _REPEAT_74(d) `_REPEAT_73(d) `REPEAT_DELIM `REPEAT_BODY(73,d) /*!< ditto */
`define _REPEAT_75(d) `_REPEAT_74(d) `REPEAT_DELIM `REPEAT_BODY(74,d) /*!< ditto */
`define _REPEAT_76(d) `_REPEAT_75(d) `REPEAT_DELIM `REPEAT_BODY(75,d) /*!< ditto */
`define _REPEAT_77(d) `_REPEAT_76(d) `REPEAT_DELIM `REPEAT_BODY(76,d) /*!< ditto */
`define _REPEAT_78(d) `_REPEAT_77(d) `REPEAT_DELIM `REPEAT_BODY(77,d) /*!< ditto */
`define _REPEAT_79(d) `_REPEAT_78(d) `REPEAT_DELIM `REPEAT_BODY(78,d) /*!< ditto */
`define _REPEAT_80(d) `_REPEAT_79(d) `REPEAT_DELIM `REPEAT_BODY(79,d) /*!< ditto */
`define _REPEAT_81(d) `_REPEAT_80(d) `REPEAT_DELIM `REPEAT_BODY(80,d) /*!< ditto */
`define _REPEAT_82(d) `_REPEAT_81(d) `REPEAT_DELIM `REPEAT_BODY(81,d) /*!< ditto */
`define _REPEAT_83(d) `_REPEAT_82(d) `REPEAT_DELIM `REPEAT_BODY(82,d) /*!< ditto */
`define _REPEAT_84(d) `_REPEAT_83(d) `REPEAT_DELIM `REPEAT_BODY(83,d) /*!< ditto */
`define _REPEAT_85(d) `_REPEAT_84(d) `REPEAT_DELIM `REPEAT_BODY(84,d) /*!< ditto */
`define _REPEAT_86(d) `_REPEAT_85(d) `REPEAT_DELIM `REPEAT_BODY(85,d) /*!< ditto */
`define _REPEAT_87(d) `_REPEAT_86(d) `REPEAT_DELIM `REPEAT_BODY(86,d) /*!< ditto */
`define _REPEAT_88(d) `_REPEAT_87(d) `REPEAT_DELIM `REPEAT_BODY(87,d) /*!< ditto */
`define _REPEAT_89(d) `_REPEAT_88(d) `REPEAT_DELIM `REPEAT_BODY(88,d) /*!< ditto */
`define _REPEAT_90(d) `_REPEAT_89(d) `REPEAT_DELIM `REPEAT_BODY(89,d) /*!< ditto */
`define _REPEAT_91(d) `_REPEAT_90(d) `REPEAT_DELIM `REPEAT_BODY(90,d) /*!< ditto */
`define _REPEAT_92(d) `_REPEAT_91(d) `REPEAT_DELIM `REPEAT_BODY(91,d) /*!< ditto */
`define _REPEAT_93(d) `_REPEAT_92(d) `REPEAT_DELIM `REPEAT_BODY(92,d) /*!< ditto */
`define _REPEAT_94(d) `_REPEAT_93(d) `REPEAT_DELIM `REPEAT_BODY(93,d) /*!< ditto */
`define _REPEAT_95(d) `_REPEAT_94(d) `REPEAT_DELIM `REPEAT_BODY(94,d) /*!< ditto */
`define _REPEAT_96(d) `_REPEAT_95(d) `REPEAT_DELIM `REPEAT_BODY(95,d) /*!< ditto */
`define _REPEAT_97(d) `_REPEAT_96(d) `REPEAT_DELIM `REPEAT_BODY(96,d) /*!< ditto */
`define _REPEAT_98(d) `_REPEAT_97(d) `REPEAT_DELIM `REPEAT_BODY(97,d) /*!< ditto */
`define _REPEAT_99(d) `_REPEAT_98(d) `REPEAT_DELIM `REPEAT_BODY(98,d) /*!< ditto */
`define _REPEAT_100(d) `_REPEAT_99(d) `REPEAT_DELIM `REPEAT_BODY(99,d)   /*!< ditto */
`define _REPEAT_101(d) `_REPEAT_100(d) `REPEAT_DELIM `REPEAT_BODY(100,d) /*!< ditto */
`define _REPEAT_102(d) `_REPEAT_101(d) `REPEAT_DELIM `REPEAT_BODY(101,d) /*!< ditto */
`define _REPEAT_103(d) `_REPEAT_102(d) `REPEAT_DELIM `REPEAT_BODY(102,d) /*!< ditto */
`define _REPEAT_104(d) `_REPEAT_103(d) `REPEAT_DELIM `REPEAT_BODY(103,d) /*!< ditto */
`define _REPEAT_105(d) `_REPEAT_104(d) `REPEAT_DELIM `REPEAT_BODY(104,d) /*!< ditto */
`define _REPEAT_106(d) `_REPEAT_105(d) `REPEAT_DELIM `REPEAT_BODY(105,d) /*!< ditto */
`define _REPEAT_107(d) `_REPEAT_106(d) `REPEAT_DELIM `REPEAT_BODY(106,d) /*!< ditto */
`define _REPEAT_108(d) `_REPEAT_107(d) `REPEAT_DELIM `REPEAT_BODY(107,d) /*!< ditto */
`define _REPEAT_109(d) `_REPEAT_108(d) `REPEAT_DELIM `REPEAT_BODY(108,d) /*!< ditto */
`define _REPEAT_110(d) `_REPEAT_109(d) `REPEAT_DELIM `REPEAT_BODY(109,d) /*!< ditto */
`define _REPEAT_111(d) `_REPEAT_110(d) `REPEAT_DELIM `REPEAT_BODY(110,d) /*!< ditto */
`define _REPEAT_112(d) `_REPEAT_111(d) `REPEAT_DELIM `REPEAT_BODY(111,d) /*!< ditto */
`define _REPEAT_113(d) `_REPEAT_112(d) `REPEAT_DELIM `REPEAT_BODY(112,d) /*!< ditto */
`define _REPEAT_114(d) `_REPEAT_113(d) `REPEAT_DELIM `REPEAT_BODY(113,d) /*!< ditto */
`define _REPEAT_115(d) `_REPEAT_114(d) `REPEAT_DELIM `REPEAT_BODY(114,d) /*!< ditto */
`define _REPEAT_116(d) `_REPEAT_115(d) `REPEAT_DELIM `REPEAT_BODY(115,d) /*!< ditto */
`define _REPEAT_117(d) `_REPEAT_116(d) `REPEAT_DELIM `REPEAT_BODY(116,d) /*!< ditto */
`define _REPEAT_118(d) `_REPEAT_117(d) `REPEAT_DELIM `REPEAT_BODY(117,d) /*!< ditto */
`define _REPEAT_119(d) `_REPEAT_118(d) `REPEAT_DELIM `REPEAT_BODY(118,d) /*!< ditto */
`define _REPEAT_120(d) `_REPEAT_119(d) `REPEAT_DELIM `REPEAT_BODY(119,d) /*!< ditto */
`define _REPEAT_121(d) `_REPEAT_120(d) `REPEAT_DELIM `REPEAT_BODY(120,d) /*!< ditto */
`define _REPEAT_122(d) `_REPEAT_121(d) `REPEAT_DELIM `REPEAT_BODY(121,d) /*!< ditto */
`define _REPEAT_123(d) `_REPEAT_122(d) `REPEAT_DELIM `REPEAT_BODY(122,d) /*!< ditto */
`define _REPEAT_124(d) `_REPEAT_123(d) `REPEAT_DELIM `REPEAT_BODY(123,d) /*!< ditto */
`define _REPEAT_125(d) `_REPEAT_124(d) `REPEAT_DELIM `REPEAT_BODY(124,d) /*!< ditto */
`define _REPEAT_126(d) `_REPEAT_125(d) `REPEAT_DELIM `REPEAT_BODY(125,d) /*!< ditto */
`define _REPEAT_127(d) `_REPEAT_126(d) `REPEAT_DELIM `REPEAT_BODY(126,d) /*!< ditto */
`define _REPEAT_128(d) `_REPEAT_127(d) `REPEAT_DELIM `REPEAT_BODY(127,d) /*!< ditto */
`define _REPEAT_129(d) `_REPEAT_128(d) `REPEAT_DELIM `REPEAT_BODY(128,d) /*!< ditto */
`define _REPEAT_130(d) `_REPEAT_129(d) `REPEAT_DELIM `REPEAT_BODY(129,d) /*!< ditto */
///@}

`endif // REPEAT_VH_INCLUDED
