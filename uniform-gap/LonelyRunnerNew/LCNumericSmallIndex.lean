import LonelyRunnerNew.LCNumericData0
import LonelyRunnerNew.LCNumericData1
import LonelyRunnerNew.LCNumericData2
import LonelyRunnerNew.LCNumericData3
import LonelyRunnerNew.LCNumericData4
import LonelyRunnerNew.LCNumericData5
import LonelyRunnerNew.LCNumericData6
import LonelyRunnerNew.LCNumericData7
import LonelyRunnerNew.LCNumericTailData
import LonelyRunnerNew.LCSmallPrimeData
import LonelyRunnerNew.LCNumericAssembly
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric.Index
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

def cuts : List ℕ := [142,147,152,157,162,167,173,179,185,191,197,203,210,217,224,231,238,246,254,262,270,279,288,297,306,316,326,336,347,358,369,381,393,405,418,431,444,458,472,487,502,518,534,551,568,586,604,623,642,662,682,703,725,747,770,794,818,843,869,896,923,951,980,1010,1041,1073,1106,1140,1175,1211,1248,1286,1325,1365,1406,1449,1493,1538,1585,1633,1682,1733,1785,1839,1895,1952,2011,2072,2135,2200,2266,2334,2405,2478,2553,2630,2709,2791,2875,2962,3051,3143,3238,3336,3437,3541,3648,3758,3871,3988,4108,4232,4359,4490,4625,4764,4907,5055,5207,5364,5525,5691,5862,6038,6220,6407,6600,6798,7002,7213,7430,7653,7883,8120,8364,8615,8874,9141,9416,9699,9990,10000]
def allBands : List Band := [Data.band_0,Data.band_1,Data.band_2,Data.band_3,Data.band_4,Data.band_5,Data.band_6,Data.band_7,Data.band_8,Data.band_9,Data.band_10,Data.band_11,Data.band_12,Data.band_13,Data.band_14,Data.band_15,Data.band_16,Data.band_17,Data.band_18,Data.band_19,Data.band_20,Data.band_21,Data.band_22,Data.band_23,Data.band_24,Data.band_25,Data.band_26,Data.band_27,Data.band_28,Data.band_29,Data.band_30,Data.band_31,Data.band_32,Data.band_33,Data.band_34,Data.band_35,Data.band_36,Data.band_37,Data.band_38,Data.band_39,Data.band_40,Data.band_41,Data.band_42,Data.band_43,Data.band_44,Data.band_45,Data.band_46,Data.band_47,Data.band_48,Data.band_49,Data.band_50,Data.band_51,Data.band_52,Data.band_53,Data.band_54,Data.band_55,Data.band_56,Data.band_57,Data.band_58,Data.band_59,Data.band_60,Data.band_61,Data.band_62,Data.band_63,Data.band_64,Data.band_65,Data.band_66,Data.band_67,Data.band_68,Data.band_69,Data.band_70,Data.band_71,Data.band_72,Data.band_73,Data.band_74,Data.band_75,Data.band_76,Data.band_77,Data.band_78,Data.band_79,Data.band_80,Data.band_81,Data.band_82,Data.band_83,Data.band_84,Data.band_85,Data.band_86,Data.band_87,Data.band_88,Data.band_89,Data.band_90,Data.band_91,Data.band_92,Data.band_93,Data.band_94,Data.band_95,Data.band_96,Data.band_97,Data.band_98,Data.band_99,Data.band_100,Data.band_101,Data.band_102,Data.band_103,Data.band_104,Data.band_105,Data.band_106,Data.band_107,Data.band_108,Data.band_109,Data.band_110,Data.band_111,Data.band_112,Data.band_113,Data.band_114,Data.band_115,Data.band_116,Data.band_117,Data.band_118,Data.band_119,Data.band_120,Data.band_121,Data.band_122,Data.band_123,Data.band_124,Data.band_125,Data.band_126,Data.band_127,Data.band_128,Data.band_129,Data.band_130,Data.band_131,Data.band_132,Data.band_133,Data.band_134,Data.band_135,Data.band_136,Data.band_137,Data.band_138,Data.band_139,Data.band_140]
def allSmallRows : List (List WeightedMarker) := [SieveData.small_0,SieveData.small_1,SieveData.small_2,SieveData.small_3,SieveData.small_4,SieveData.small_5,SieveData.small_6,SieveData.small_7,SieveData.small_8,SieveData.small_9,SieveData.small_10,SieveData.small_11,SieveData.small_12,SieveData.small_13,SieveData.small_14,SieveData.small_15,SieveData.small_16,SieveData.small_17,SieveData.small_18,SieveData.small_19,SieveData.small_20,SieveData.small_21,SieveData.small_22,SieveData.small_23,SieveData.small_24,SieveData.small_25,SieveData.small_26,SieveData.small_27,SieveData.small_28,SieveData.small_29,SieveData.small_30,SieveData.small_31,SieveData.small_32,SieveData.small_33,SieveData.small_34,SieveData.small_35,SieveData.small_36,SieveData.small_37,SieveData.small_38,SieveData.small_39,SieveData.small_40,SieveData.small_41,SieveData.small_42,SieveData.small_43,SieveData.small_44,SieveData.small_45,SieveData.small_46,SieveData.small_47,SieveData.small_48,SieveData.small_49,SieveData.small_50,SieveData.small_51,SieveData.small_52,SieveData.small_53,SieveData.small_54,SieveData.small_55,SieveData.small_56,SieveData.small_57,SieveData.small_58,SieveData.small_59,SieveData.small_60,SieveData.small_61,SieveData.small_62,SieveData.small_63,SieveData.small_64,SieveData.small_65,SieveData.small_66,SieveData.small_67,SieveData.small_68,SieveData.small_69,SieveData.small_70,SieveData.small_71,SieveData.small_72,SieveData.small_73,SieveData.small_74,SieveData.small_75,SieveData.small_76,SieveData.small_77,SieveData.small_78,SieveData.small_79,SieveData.small_80,SieveData.small_81,SieveData.small_82,SieveData.small_83,SieveData.small_84,SieveData.small_85,SieveData.small_86,SieveData.small_87,SieveData.small_88,SieveData.small_89,SieveData.small_90,SieveData.small_91,SieveData.small_92,SieveData.small_93,SieveData.small_94,SieveData.small_95,SieveData.small_96,SieveData.small_97,SieveData.small_98,SieveData.small_99,SieveData.small_100,SieveData.small_101,SieveData.small_102,SieveData.small_103,SieveData.small_104,SieveData.small_105,SieveData.small_106,SieveData.small_107,SieveData.small_108,SieveData.small_109,SieveData.small_110,SieveData.small_111,SieveData.small_112,SieveData.small_113,SieveData.small_114,SieveData.small_115,SieveData.small_116,SieveData.small_117,SieveData.small_118,SieveData.small_119,SieveData.small_120,SieveData.small_121,SieveData.small_122,SieveData.small_123,SieveData.small_124,SieveData.small_125,SieveData.small_126,SieveData.small_127,SieveData.small_128,SieveData.small_129,SieveData.small_130,SieveData.small_131,SieveData.small_132,SieveData.small_133,SieveData.small_134,SieveData.small_135,SieveData.small_136,SieveData.small_137,SieveData.small_138,SieveData.small_139,SieveData.small_140]
def smallCoefficients : List ℚ := [(24435881/1000000:ℚ),(3002817/125000:ℚ),(1473713/62500:ℚ),(23175569/1000000:ℚ),(22805687/1000000:ℚ),(22465369/1000000:ℚ),(22090949/1000000:ℚ),(21748729/1000000:ℚ),(10717233/500000:ℚ),(422893/20000:ℚ),(20876353/1000000:ℚ),(20627107/1000000:ℚ),(10178817/500000:ℚ),(10054223/500000:ℚ),(310581/15625:ℚ),(19661847/1000000:ℚ),(19460727/1000000:ℚ),(19246411/1000000:ℚ),(19046871/1000000:ℚ),(2357563/125000:ℚ),(3737187/200000:ℚ),(18502173/1000000:ℚ),(1833039/100000:ℚ),(18169341/1000000:ℚ),(18017957/1000000:ℚ),(17859973/1000000:ℚ),(8855847/500000:ℚ),(17572177/1000000:ℚ),(17427861/1000000:ℚ),(8646109/500000:ℚ),(1072777/62500:ℚ),(8516577/500000:ℚ),(16909571/1000000:ℚ),(8396487/500000:ℚ),(16673827/1000000:ℚ),(4140367/250000:ℚ),(16455289/1000000:ℚ),(3269449/200000:ℚ),(16245163/1000000:ℚ),(16141829/1000000:ℚ),(4011047/250000:ℚ),(7972883/500000:ℚ),(15852741/1000000:ℚ),(3151859/200000:ℚ),(15670927/1000000:ℚ),(15582421/1000000:ℚ),(15498667/1000000:ℚ),(240859/15625:ℚ),(15335717/1000000:ℚ),(7628337/500000:ℚ),(3795439/250000:ℚ),(377679/25000:ℚ),(15033109/1000000:ℚ),(14962901/1000000:ℚ),(1861659/125000:ℚ),(231631/15625:ℚ),(1844879/125000:ℚ),(1836801/125000:ℚ),(3657657/250000:ℚ),(14567793/1000000:ℚ),(7254069/500000:ℚ),(14449361/1000000:ℚ),(7195767/500000:ℚ),(7167357/500000:ℚ),(14278949/1000000:ℚ),(3556069/250000:ℚ),(14170723/1000000:ℚ),(1411831/100000:ℚ),(14067049/1000000:ℚ),(2803389/200000:ℚ),(13967999/1000000:ℚ),(6960103/500000:ℚ),(13873559/1000000:ℚ),(13828047/1000000:ℚ),(13783653/1000000:ℚ),(6869679/500000:ℚ),(3424061/250000:ℚ),(13654281/1000000:ℚ),(13612577/1000000:ℚ),(848253/62500:ℚ),(13532659/1000000:ℚ),(6746813/500000:ℚ),(3363933/250000:ℚ),(13418257/1000000:ℚ),(13381259/1000000:ℚ),(13345399/1000000:ℚ),(2662009/200000:ℚ),(3318809/250000:ℚ),(6620501/500000:ℚ),(13207367/1000000:ℚ),(13174833/1000000:ℚ),(1642861/125000:ℚ),(1311111/100000:ℚ),(6539993/500000:ℚ),(163119/12500:ℚ),(6509857/500000:ℚ),(6495283/500000:ℚ),(12961729/1000000:ℚ),(12933573/1000000:ℚ),(516231/40000:ℚ),(12878667/1000000:ℚ),(12851949/1000000:ℚ),(801603/62500:ℚ),(6399891/500000:ℚ),(12774369/1000000:ℚ),(637471/50000:ℚ),(12724947/1000000:ℚ),(6350477/500000:ℚ),(12677447/1000000:ℚ),(6327117/500000:ℚ),(12631527/1000000:ℚ),(2521829/200000:ℚ),(12587277/1000000:ℚ),(12565757/1000000:ℚ),(12544597/1000000:ℚ),(12523811/1000000:ℚ),(2500681/200000:ℚ),(6241627/500000:ℚ),(12463507/1000000:ℚ),(2488809/200000:ℚ),(12424999/1000000:ℚ),(6203129/500000:ℚ),(1548479/125000:ℚ),(12369731/1000000:ℚ),(6175933/500000:ℚ),(12334347/1000000:ℚ),(12317089/1000000:ℚ),(12300189/1000000:ℚ),(2456713/200000:ℚ),(766697/62500:ℚ),(12251039/1000000:ℚ),(12235231/1000000:ℚ),(763729/62500:ℚ),(244087/20000:ℚ),(761831/62500:ℚ),(1217451/100000:ℚ),(12159941/1000000:ℚ),(7591/625:ℚ),(12131497/1000000:ℚ),(6058819/500000:ℚ),(12104029/1000000:ℚ)]
def smallMoments : List ℚ := [(0/1:ℚ),(14127929249337/12500000000000000:ℚ),(527883189695523/1000000000000000000:ℚ),(0/1:ℚ),(61284575283699/62500000000000000:ℚ),(228350878232499/500000000000000000:ℚ),(434043033005327/1000000000000000000:ℚ),(213452128377401/500000000000000000:ℚ),(393978557903729/1000000000000000000:ℚ),(764104700986019/1000000000000000000:ℚ),(74114980899751/200000000000000000:ℚ),(0/1:ℚ),(169782026452263/500000000000000000:ℚ),(312656432810543/1000000000000000000:ℚ),(302489147773199/500000000000000000:ℚ),(292841723158153/1000000000000000000:ℚ),(280194710764517/500000000000000000:ℚ),(65514501270043/250000000000000000:ℚ),(31622405510877/125000000000000000:ℚ),(48073576322723/100000000000000000:ℚ),(229965755919091/500000000000000000:ℚ),(440506105996699/1000000000000000000:ℚ),(208021406915197/1000000000000000000:ℚ),(0/1:ℚ),(572831289908447/1000000000000000000:ℚ),(184959110450683/1000000000000000000:ℚ),(43351357804529/250000000000000000:ℚ),(165212979811553/500000000000000000:ℚ),(31775352611233/100000000000000000:ℚ),(15112695724213/50000000000000000:ℚ),(286759276426139/1000000000000000000:ℚ),(5514812131901/20000000000000000:ℚ),(65605644101353/250000000000000000:ℚ),(15805765104847/125000000000000000:ℚ),(72001637503279/200000000000000000:ℚ),(171068745886741/500000000000000000:ℚ),(43430747543897/200000000000000000:ℚ),(314581244310509/1000000000000000000:ℚ),(98665237640461/500000000000000000:ℚ),(23779020243243/125000000000000000:ℚ),(184082644572683/1000000000000000000:ℚ),(175714794533231/1000000000000000000:ℚ),(10326452428373/62500000000000000:ℚ),(158226785535543/1000000000000000000:ℚ),(229750020848143/1000000000000000000:ℚ),(289107010699853/1000000000000000000:ℚ),(34480207589799/125000000000000000:ℚ),(65431304331823/500000000000000000:ℚ),(2459708459011/7812500000000000:ℚ),(2394559492201/20000000000000000:ℚ),(86602547382103/500000000000000000:ℚ),(22021583536567/200000000000000000:ℚ),(26335609773689/125000000000000000:ℚ),(25103516660837/125000000000000000:ℚ),(96501919356247/1000000000000000000:ℚ),(137918884937751/1000000000000000000:ℚ),(220751424784881/1000000000000000000:ℚ),(41848031158381/250000000000000000:ℚ),(160639270268443/1000000000000000000:ℚ),(2291056144711/20000000000000000:ℚ),(36607511517711/250000000000000000:ℚ),(140044937334393/1000000000000000000:ℚ),(16775690894849/125000000000000000:ℚ),(96146532950571/500000000000000000:ℚ),(38231879845311/250000000000000000:ℚ),(72777110304807/500000000000000000:ℚ),(112541602236029/1000000000000000000:ℚ),(21359464286321/200000000000000000:ℚ),(102671584952141/1000000000000000000:ℚ),(73790345272479/500000000000000000:ℚ),(116632648102137/1000000000000000000:ℚ),(7174443344449/40000000000000000:ℚ),(21422818824871/500000000000000000:ℚ),(82363429920367/1000000000000000000:ℚ),(3418418836567/25000000000000000:ℚ),(83974923933899/500000000000000000:ℚ),(35790644415509/500000000000000000:ℚ),(136787642963017/1000000000000000000:ℚ),(130649308004801/1000000000000000000:ℚ),(15647860392811/200000000000000000:ℚ),(26148990816041/250000000000000000:ℚ),(42966803538047/500000000000000000:ℚ),(41310066019227/500000000000000000:ℚ),(52308637404593/500000000000000000:ℚ),(87610430945899/1000000000000000000:ℚ),(23795879448409/250000000000000000:ℚ),(5017927237607/62500000000000000:ℚ),(49425160981237/500000000000000000:ℚ),(63634869944669/1000000000000000000:ℚ),(80651407452729/1000000000000000000:ℚ),(75440713559/781250000000000:ℚ),(4412005729979/40000000000000000:ℚ),(87676236245661/1000000000000000000:ℚ),(29095646709981/500000000000000000:ℚ),(14037579037003/250000000000000000:ℚ),(99717195329617/1000000000000000000:ℚ),(2762914679491/31250000000000000:ℚ),(70483271377911/1000000000000000000:ℚ),(67384340212501/1000000000000000000:ℚ),(70811618328169/1000000000000000000:ℚ),(5547799000067/100000000000000000:ℚ),(1294359957253/20000000000000000:ℚ),(7308207400597/100000000000000000:ℚ),(59468009974147/1000000000000000000:ℚ),(77105746806137/1000000000000000000:ℚ),(34492984146973/500000000000000000:ℚ),(28351305285489/500000000000000000:ℚ),(63282562207027/1000000000000000000:ℚ),(56377380448809/1000000000000000000:ℚ),(66252571255911/1000000000000000000:ℚ),(59228773687403/1000000000000000000:ℚ),(56791910116637/1000000000000000000:ℚ),(25291199141517/500000000000000000:ℚ),(52004574797177/1000000000000000000:ℚ),(56413187398917/1000000000000000000:ℚ),(8888811415701/200000000000000000:ℚ),(3983262707251/62500000000000000:ℚ),(23223387643343/500000000000000000:ℚ),(8890533977757/200000000000000000:ℚ),(14582177283727/250000000000000000:ℚ),(1926305201757/40000000000000000:ℚ),(26659988699449/500000000000000000:ℚ),(149072022197/4000000000000000:ℚ),(48962077316759/1000000000000000000:ℚ),(6649176355827/125000000000000000:ℚ),(38565900303937/1000000000000000000:ℚ),(2674176865887/62500000000000000:ℚ),(4836825552097/100000000000000000:ℚ),(18692431632363/500000000000000000:ℚ),(32488198556997/1000000000000000000:ℚ),(24479181307847/500000000000000000:ℚ),(40567196963619/1000000000000000000:ℚ),(35785028460999/1000000000000000000:ℚ),(4643516450377/125000000000000000:ℚ),(17098034292611/500000000000000000:ℚ),(8900164074717/200000000000000000:ℚ),(1055361653877/31250000000000000:ℚ),(37141145205591/1000000000000000000:ℚ),(18937887684597/500000000000000000:ℚ),(109747517789/3125000000000000:ℚ),(0/1:ℚ)]
def smallBand (i : Fin 141) : Band := allBands[i.val]!
def smallRows (i : Fin 141) : List WeightedMarker := allSmallRows[i.val]!
def smallLo (i : Fin 141) : ℕ := cuts[i.val]!+1
def smallHi (i : Fin 141) : ℕ := cuts[i.val+1]!+1
def smallCoefficient (i : Fin 141) : ℚ := smallCoefficients[i.val]!
def smallMoment (i : Fin 141) : ℚ := smallMoments[i.val]!

theorem small_band_valid (i : Fin 141) : (smallBand i).Valid Data.boxes := by
  fin_cases i
  · exact Data.band_0_valid
  · exact Data.band_1_valid
  · exact Data.band_2_valid
  · exact Data.band_3_valid
  · exact Data.band_4_valid
  · exact Data.band_5_valid
  · exact Data.band_6_valid
  · exact Data.band_7_valid
  · exact Data.band_8_valid
  · exact Data.band_9_valid
  · exact Data.band_10_valid
  · exact Data.band_11_valid
  · exact Data.band_12_valid
  · exact Data.band_13_valid
  · exact Data.band_14_valid
  · exact Data.band_15_valid
  · exact Data.band_16_valid
  · exact Data.band_17_valid
  · exact Data.band_18_valid
  · exact Data.band_19_valid
  · exact Data.band_20_valid
  · exact Data.band_21_valid
  · exact Data.band_22_valid
  · exact Data.band_23_valid
  · exact Data.band_24_valid
  · exact Data.band_25_valid
  · exact Data.band_26_valid
  · exact Data.band_27_valid
  · exact Data.band_28_valid
  · exact Data.band_29_valid
  · exact Data.band_30_valid
  · exact Data.band_31_valid
  · exact Data.band_32_valid
  · exact Data.band_33_valid
  · exact Data.band_34_valid
  · exact Data.band_35_valid
  · exact Data.band_36_valid
  · exact Data.band_37_valid
  · exact Data.band_38_valid
  · exact Data.band_39_valid
  · exact Data.band_40_valid
  · exact Data.band_41_valid
  · exact Data.band_42_valid
  · exact Data.band_43_valid
  · exact Data.band_44_valid
  · exact Data.band_45_valid
  · exact Data.band_46_valid
  · exact Data.band_47_valid
  · exact Data.band_48_valid
  · exact Data.band_49_valid
  · exact Data.band_50_valid
  · exact Data.band_51_valid
  · exact Data.band_52_valid
  · exact Data.band_53_valid
  · exact Data.band_54_valid
  · exact Data.band_55_valid
  · exact Data.band_56_valid
  · exact Data.band_57_valid
  · exact Data.band_58_valid
  · exact Data.band_59_valid
  · exact Data.band_60_valid
  · exact Data.band_61_valid
  · exact Data.band_62_valid
  · exact Data.band_63_valid
  · exact Data.band_64_valid
  · exact Data.band_65_valid
  · exact Data.band_66_valid
  · exact Data.band_67_valid
  · exact Data.band_68_valid
  · exact Data.band_69_valid
  · exact Data.band_70_valid
  · exact Data.band_71_valid
  · exact Data.band_72_valid
  · exact Data.band_73_valid
  · exact Data.band_74_valid
  · exact Data.band_75_valid
  · exact Data.band_76_valid
  · exact Data.band_77_valid
  · exact Data.band_78_valid
  · exact Data.band_79_valid
  · exact Data.band_80_valid
  · exact Data.band_81_valid
  · exact Data.band_82_valid
  · exact Data.band_83_valid
  · exact Data.band_84_valid
  · exact Data.band_85_valid
  · exact Data.band_86_valid
  · exact Data.band_87_valid
  · exact Data.band_88_valid
  · exact Data.band_89_valid
  · exact Data.band_90_valid
  · exact Data.band_91_valid
  · exact Data.band_92_valid
  · exact Data.band_93_valid
  · exact Data.band_94_valid
  · exact Data.band_95_valid
  · exact Data.band_96_valid
  · exact Data.band_97_valid
  · exact Data.band_98_valid
  · exact Data.band_99_valid
  · exact Data.band_100_valid
  · exact Data.band_101_valid
  · exact Data.band_102_valid
  · exact Data.band_103_valid
  · exact Data.band_104_valid
  · exact Data.band_105_valid
  · exact Data.band_106_valid
  · exact Data.band_107_valid
  · exact Data.band_108_valid
  · exact Data.band_109_valid
  · exact Data.band_110_valid
  · exact Data.band_111_valid
  · exact Data.band_112_valid
  · exact Data.band_113_valid
  · exact Data.band_114_valid
  · exact Data.band_115_valid
  · exact Data.band_116_valid
  · exact Data.band_117_valid
  · exact Data.band_118_valid
  · exact Data.band_119_valid
  · exact Data.band_120_valid
  · exact Data.band_121_valid
  · exact Data.band_122_valid
  · exact Data.band_123_valid
  · exact Data.band_124_valid
  · exact Data.band_125_valid
  · exact Data.band_126_valid
  · exact Data.band_127_valid
  · exact Data.band_128_valid
  · exact Data.band_129_valid
  · exact Data.band_130_valid
  · exact Data.band_131_valid
  · exact Data.band_132_valid
  · exact Data.band_133_valid
  · exact Data.band_134_valid
  · exact Data.band_135_valid
  · exact Data.band_136_valid
  · exact Data.band_137_valid
  · exact Data.band_138_valid
  · exact Data.band_139_valid
  · exact Data.band_140_valid

theorem small_band_lower (i : Fin 141) : (smallBand i).lower+1=smallLo i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem small_sieve_valid (i : Fin 141) : WeightedSieveValid (smallLo i) (smallRows i) := by
  fin_cases i
  · exact SieveData.small_0_valid
  · exact SieveData.small_1_valid
  · exact SieveData.small_2_valid
  · exact SieveData.small_3_valid
  · exact SieveData.small_4_valid
  · exact SieveData.small_5_valid
  · exact SieveData.small_6_valid
  · exact SieveData.small_7_valid
  · exact SieveData.small_8_valid
  · exact SieveData.small_9_valid
  · exact SieveData.small_10_valid
  · exact SieveData.small_11_valid
  · exact SieveData.small_12_valid
  · exact SieveData.small_13_valid
  · exact SieveData.small_14_valid
  · exact SieveData.small_15_valid
  · exact SieveData.small_16_valid
  · exact SieveData.small_17_valid
  · exact SieveData.small_18_valid
  · exact SieveData.small_19_valid
  · exact SieveData.small_20_valid
  · exact SieveData.small_21_valid
  · exact SieveData.small_22_valid
  · exact SieveData.small_23_valid
  · exact SieveData.small_24_valid
  · exact SieveData.small_25_valid
  · exact SieveData.small_26_valid
  · exact SieveData.small_27_valid
  · exact SieveData.small_28_valid
  · exact SieveData.small_29_valid
  · exact SieveData.small_30_valid
  · exact SieveData.small_31_valid
  · exact SieveData.small_32_valid
  · exact SieveData.small_33_valid
  · exact SieveData.small_34_valid
  · exact SieveData.small_35_valid
  · exact SieveData.small_36_valid
  · exact SieveData.small_37_valid
  · exact SieveData.small_38_valid
  · exact SieveData.small_39_valid
  · exact SieveData.small_40_valid
  · exact SieveData.small_41_valid
  · exact SieveData.small_42_valid
  · exact SieveData.small_43_valid
  · exact SieveData.small_44_valid
  · exact SieveData.small_45_valid
  · exact SieveData.small_46_valid
  · exact SieveData.small_47_valid
  · exact SieveData.small_48_valid
  · exact SieveData.small_49_valid
  · exact SieveData.small_50_valid
  · exact SieveData.small_51_valid
  · exact SieveData.small_52_valid
  · exact SieveData.small_53_valid
  · exact SieveData.small_54_valid
  · exact SieveData.small_55_valid
  · exact SieveData.small_56_valid
  · exact SieveData.small_57_valid
  · exact SieveData.small_58_valid
  · exact SieveData.small_59_valid
  · exact SieveData.small_60_valid
  · exact SieveData.small_61_valid
  · exact SieveData.small_62_valid
  · exact SieveData.small_63_valid
  · exact SieveData.small_64_valid
  · exact SieveData.small_65_valid
  · exact SieveData.small_66_valid
  · exact SieveData.small_67_valid
  · exact SieveData.small_68_valid
  · exact SieveData.small_69_valid
  · exact SieveData.small_70_valid
  · exact SieveData.small_71_valid
  · exact SieveData.small_72_valid
  · exact SieveData.small_73_valid
  · exact SieveData.small_74_valid
  · exact SieveData.small_75_valid
  · exact SieveData.small_76_valid
  · exact SieveData.small_77_valid
  · exact SieveData.small_78_valid
  · exact SieveData.small_79_valid
  · exact SieveData.small_80_valid
  · exact SieveData.small_81_valid
  · exact SieveData.small_82_valid
  · exact SieveData.small_83_valid
  · exact SieveData.small_84_valid
  · exact SieveData.small_85_valid
  · exact SieveData.small_86_valid
  · exact SieveData.small_87_valid
  · exact SieveData.small_88_valid
  · exact SieveData.small_89_valid
  · exact SieveData.small_90_valid
  · exact SieveData.small_91_valid
  · exact SieveData.small_92_valid
  · exact SieveData.small_93_valid
  · exact SieveData.small_94_valid
  · exact SieveData.small_95_valid
  · exact SieveData.small_96_valid
  · exact SieveData.small_97_valid
  · exact SieveData.small_98_valid
  · exact SieveData.small_99_valid
  · exact SieveData.small_100_valid
  · exact SieveData.small_101_valid
  · exact SieveData.small_102_valid
  · exact SieveData.small_103_valid
  · exact SieveData.small_104_valid
  · exact SieveData.small_105_valid
  · exact SieveData.small_106_valid
  · exact SieveData.small_107_valid
  · exact SieveData.small_108_valid
  · exact SieveData.small_109_valid
  · exact SieveData.small_110_valid
  · exact SieveData.small_111_valid
  · exact SieveData.small_112_valid
  · exact SieveData.small_113_valid
  · exact SieveData.small_114_valid
  · exact SieveData.small_115_valid
  · exact SieveData.small_116_valid
  · exact SieveData.small_117_valid
  · exact SieveData.small_118_valid
  · exact SieveData.small_119_valid
  · exact SieveData.small_120_valid
  · exact SieveData.small_121_valid
  · exact SieveData.small_122_valid
  · exact SieveData.small_123_valid
  · exact SieveData.small_124_valid
  · exact SieveData.small_125_valid
  · exact SieveData.small_126_valid
  · exact SieveData.small_127_valid
  · exact SieveData.small_128_valid
  · exact SieveData.small_129_valid
  · exact SieveData.small_130_valid
  · exact SieveData.small_131_valid
  · exact SieveData.small_132_valid
  · exact SieveData.small_133_valid
  · exact SieveData.small_134_valid
  · exact SieveData.small_135_valid
  · exact SieveData.small_136_valid
  · exact SieveData.small_137_valid
  · exact SieveData.small_138_valid
  · exact SieveData.small_139_valid
  · exact SieveData.small_140_valid

theorem small_sieve_length (i : Fin 141) : (smallRows i).length=smallHi i-smallLo i := by
  fin_cases i
  · exact SieveData.small_0_length
  · exact SieveData.small_1_length
  · exact SieveData.small_2_length
  · exact SieveData.small_3_length
  · exact SieveData.small_4_length
  · exact SieveData.small_5_length
  · exact SieveData.small_6_length
  · exact SieveData.small_7_length
  · exact SieveData.small_8_length
  · exact SieveData.small_9_length
  · exact SieveData.small_10_length
  · exact SieveData.small_11_length
  · exact SieveData.small_12_length
  · exact SieveData.small_13_length
  · exact SieveData.small_14_length
  · exact SieveData.small_15_length
  · exact SieveData.small_16_length
  · exact SieveData.small_17_length
  · exact SieveData.small_18_length
  · exact SieveData.small_19_length
  · exact SieveData.small_20_length
  · exact SieveData.small_21_length
  · exact SieveData.small_22_length
  · exact SieveData.small_23_length
  · exact SieveData.small_24_length
  · exact SieveData.small_25_length
  · exact SieveData.small_26_length
  · exact SieveData.small_27_length
  · exact SieveData.small_28_length
  · exact SieveData.small_29_length
  · exact SieveData.small_30_length
  · exact SieveData.small_31_length
  · exact SieveData.small_32_length
  · exact SieveData.small_33_length
  · exact SieveData.small_34_length
  · exact SieveData.small_35_length
  · exact SieveData.small_36_length
  · exact SieveData.small_37_length
  · exact SieveData.small_38_length
  · exact SieveData.small_39_length
  · exact SieveData.small_40_length
  · exact SieveData.small_41_length
  · exact SieveData.small_42_length
  · exact SieveData.small_43_length
  · exact SieveData.small_44_length
  · exact SieveData.small_45_length
  · exact SieveData.small_46_length
  · exact SieveData.small_47_length
  · exact SieveData.small_48_length
  · exact SieveData.small_49_length
  · exact SieveData.small_50_length
  · exact SieveData.small_51_length
  · exact SieveData.small_52_length
  · exact SieveData.small_53_length
  · exact SieveData.small_54_length
  · exact SieveData.small_55_length
  · exact SieveData.small_56_length
  · exact SieveData.small_57_length
  · exact SieveData.small_58_length
  · exact SieveData.small_59_length
  · exact SieveData.small_60_length
  · exact SieveData.small_61_length
  · exact SieveData.small_62_length
  · exact SieveData.small_63_length
  · exact SieveData.small_64_length
  · exact SieveData.small_65_length
  · exact SieveData.small_66_length
  · exact SieveData.small_67_length
  · exact SieveData.small_68_length
  · exact SieveData.small_69_length
  · exact SieveData.small_70_length
  · exact SieveData.small_71_length
  · exact SieveData.small_72_length
  · exact SieveData.small_73_length
  · exact SieveData.small_74_length
  · exact SieveData.small_75_length
  · exact SieveData.small_76_length
  · exact SieveData.small_77_length
  · exact SieveData.small_78_length
  · exact SieveData.small_79_length
  · exact SieveData.small_80_length
  · exact SieveData.small_81_length
  · exact SieveData.small_82_length
  · exact SieveData.small_83_length
  · exact SieveData.small_84_length
  · exact SieveData.small_85_length
  · exact SieveData.small_86_length
  · exact SieveData.small_87_length
  · exact SieveData.small_88_length
  · exact SieveData.small_89_length
  · exact SieveData.small_90_length
  · exact SieveData.small_91_length
  · exact SieveData.small_92_length
  · exact SieveData.small_93_length
  · exact SieveData.small_94_length
  · exact SieveData.small_95_length
  · exact SieveData.small_96_length
  · exact SieveData.small_97_length
  · exact SieveData.small_98_length
  · exact SieveData.small_99_length
  · exact SieveData.small_100_length
  · exact SieveData.small_101_length
  · exact SieveData.small_102_length
  · exact SieveData.small_103_length
  · exact SieveData.small_104_length
  · exact SieveData.small_105_length
  · exact SieveData.small_106_length
  · exact SieveData.small_107_length
  · exact SieveData.small_108_length
  · exact SieveData.small_109_length
  · exact SieveData.small_110_length
  · exact SieveData.small_111_length
  · exact SieveData.small_112_length
  · exact SieveData.small_113_length
  · exact SieveData.small_114_length
  · exact SieveData.small_115_length
  · exact SieveData.small_116_length
  · exact SieveData.small_117_length
  · exact SieveData.small_118_length
  · exact SieveData.small_119_length
  · exact SieveData.small_120_length
  · exact SieveData.small_121_length
  · exact SieveData.small_122_length
  · exact SieveData.small_123_length
  · exact SieveData.small_124_length
  · exact SieveData.small_125_length
  · exact SieveData.small_126_length
  · exact SieveData.small_127_length
  · exact SieveData.small_128_length
  · exact SieveData.small_129_length
  · exact SieveData.small_130_length
  · exact SieveData.small_131_length
  · exact SieveData.small_132_length
  · exact SieveData.small_133_length
  · exact SieveData.small_134_length
  · exact SieveData.small_135_length
  · exact SieveData.small_136_length
  · exact SieveData.small_137_length
  · exact SieveData.small_138_length
  · exact SieveData.small_139_length
  · exact SieveData.small_140_length

theorem small_sieve_sum (i : Fin 141) : weightedSieveSum (smallRows i)=smallMoment i := by
  fin_cases i
  · exact SieveData.small_0_sum
  · exact SieveData.small_1_sum
  · exact SieveData.small_2_sum
  · exact SieveData.small_3_sum
  · exact SieveData.small_4_sum
  · exact SieveData.small_5_sum
  · exact SieveData.small_6_sum
  · exact SieveData.small_7_sum
  · exact SieveData.small_8_sum
  · exact SieveData.small_9_sum
  · exact SieveData.small_10_sum
  · exact SieveData.small_11_sum
  · exact SieveData.small_12_sum
  · exact SieveData.small_13_sum
  · exact SieveData.small_14_sum
  · exact SieveData.small_15_sum
  · exact SieveData.small_16_sum
  · exact SieveData.small_17_sum
  · exact SieveData.small_18_sum
  · exact SieveData.small_19_sum
  · exact SieveData.small_20_sum
  · exact SieveData.small_21_sum
  · exact SieveData.small_22_sum
  · exact SieveData.small_23_sum
  · exact SieveData.small_24_sum
  · exact SieveData.small_25_sum
  · exact SieveData.small_26_sum
  · exact SieveData.small_27_sum
  · exact SieveData.small_28_sum
  · exact SieveData.small_29_sum
  · exact SieveData.small_30_sum
  · exact SieveData.small_31_sum
  · exact SieveData.small_32_sum
  · exact SieveData.small_33_sum
  · exact SieveData.small_34_sum
  · exact SieveData.small_35_sum
  · exact SieveData.small_36_sum
  · exact SieveData.small_37_sum
  · exact SieveData.small_38_sum
  · exact SieveData.small_39_sum
  · exact SieveData.small_40_sum
  · exact SieveData.small_41_sum
  · exact SieveData.small_42_sum
  · exact SieveData.small_43_sum
  · exact SieveData.small_44_sum
  · exact SieveData.small_45_sum
  · exact SieveData.small_46_sum
  · exact SieveData.small_47_sum
  · exact SieveData.small_48_sum
  · exact SieveData.small_49_sum
  · exact SieveData.small_50_sum
  · exact SieveData.small_51_sum
  · exact SieveData.small_52_sum
  · exact SieveData.small_53_sum
  · exact SieveData.small_54_sum
  · exact SieveData.small_55_sum
  · exact SieveData.small_56_sum
  · exact SieveData.small_57_sum
  · exact SieveData.small_58_sum
  · exact SieveData.small_59_sum
  · exact SieveData.small_60_sum
  · exact SieveData.small_61_sum
  · exact SieveData.small_62_sum
  · exact SieveData.small_63_sum
  · exact SieveData.small_64_sum
  · exact SieveData.small_65_sum
  · exact SieveData.small_66_sum
  · exact SieveData.small_67_sum
  · exact SieveData.small_68_sum
  · exact SieveData.small_69_sum
  · exact SieveData.small_70_sum
  · exact SieveData.small_71_sum
  · exact SieveData.small_72_sum
  · exact SieveData.small_73_sum
  · exact SieveData.small_74_sum
  · exact SieveData.small_75_sum
  · exact SieveData.small_76_sum
  · exact SieveData.small_77_sum
  · exact SieveData.small_78_sum
  · exact SieveData.small_79_sum
  · exact SieveData.small_80_sum
  · exact SieveData.small_81_sum
  · exact SieveData.small_82_sum
  · exact SieveData.small_83_sum
  · exact SieveData.small_84_sum
  · exact SieveData.small_85_sum
  · exact SieveData.small_86_sum
  · exact SieveData.small_87_sum
  · exact SieveData.small_88_sum
  · exact SieveData.small_89_sum
  · exact SieveData.small_90_sum
  · exact SieveData.small_91_sum
  · exact SieveData.small_92_sum
  · exact SieveData.small_93_sum
  · exact SieveData.small_94_sum
  · exact SieveData.small_95_sum
  · exact SieveData.small_96_sum
  · exact SieveData.small_97_sum
  · exact SieveData.small_98_sum
  · exact SieveData.small_99_sum
  · exact SieveData.small_100_sum
  · exact SieveData.small_101_sum
  · exact SieveData.small_102_sum
  · exact SieveData.small_103_sum
  · exact SieveData.small_104_sum
  · exact SieveData.small_105_sum
  · exact SieveData.small_106_sum
  · exact SieveData.small_107_sum
  · exact SieveData.small_108_sum
  · exact SieveData.small_109_sum
  · exact SieveData.small_110_sum
  · exact SieveData.small_111_sum
  · exact SieveData.small_112_sum
  · exact SieveData.small_113_sum
  · exact SieveData.small_114_sum
  · exact SieveData.small_115_sum
  · exact SieveData.small_116_sum
  · exact SieveData.small_117_sum
  · exact SieveData.small_118_sum
  · exact SieveData.small_119_sum
  · exact SieveData.small_120_sum
  · exact SieveData.small_121_sum
  · exact SieveData.small_122_sum
  · exact SieveData.small_123_sum
  · exact SieveData.small_124_sum
  · exact SieveData.small_125_sum
  · exact SieveData.small_126_sum
  · exact SieveData.small_127_sum
  · exact SieveData.small_128_sum
  · exact SieveData.small_129_sum
  · exact SieveData.small_130_sum
  · exact SieveData.small_131_sum
  · exact SieveData.small_132_sum
  · exact SieveData.small_133_sum
  · exact SieveData.small_134_sum
  · exact SieveData.small_135_sum
  · exact SieveData.small_136_sum
  · exact SieveData.small_137_sum
  · exact SieveData.small_138_sum
  · exact SieveData.small_139_sum
  · exact SieveData.small_140_sum

theorem small_coefficient_eq (i : Fin 141) : lastCoefficient (smallBand i).steps=smallCoefficient i := by
  fin_cases i
  · change lastCoefficient Data.steps_0=(24435881/1000000:ℚ); norm_num [lastCoefficient,Data.steps_0]
  · change lastCoefficient Data.steps_1=(3002817/125000:ℚ); norm_num [lastCoefficient,Data.steps_1]
  · change lastCoefficient Data.steps_2=(1473713/62500:ℚ); norm_num [lastCoefficient,Data.steps_2]
  · change lastCoefficient Data.steps_3=(23175569/1000000:ℚ); norm_num [lastCoefficient,Data.steps_3]
  · change lastCoefficient Data.steps_4=(22805687/1000000:ℚ); norm_num [lastCoefficient,Data.steps_4]
  · change lastCoefficient Data.steps_5=(22465369/1000000:ℚ); norm_num [lastCoefficient,Data.steps_5]
  · change lastCoefficient Data.steps_6=(22090949/1000000:ℚ); norm_num [lastCoefficient,Data.steps_6]
  · change lastCoefficient Data.steps_7=(21748729/1000000:ℚ); norm_num [lastCoefficient,Data.steps_7]
  · change lastCoefficient Data.steps_8=(10717233/500000:ℚ); norm_num [lastCoefficient,Data.steps_8]
  · change lastCoefficient Data.steps_9=(422893/20000:ℚ); norm_num [lastCoefficient,Data.steps_9]
  · change lastCoefficient Data.steps_10=(20876353/1000000:ℚ); norm_num [lastCoefficient,Data.steps_10]
  · change lastCoefficient Data.steps_11=(20627107/1000000:ℚ); norm_num [lastCoefficient,Data.steps_11]
  · change lastCoefficient Data.steps_12=(10178817/500000:ℚ); norm_num [lastCoefficient,Data.steps_12]
  · change lastCoefficient Data.steps_13=(10054223/500000:ℚ); norm_num [lastCoefficient,Data.steps_13]
  · change lastCoefficient Data.steps_14=(310581/15625:ℚ); norm_num [lastCoefficient,Data.steps_14]
  · change lastCoefficient Data.steps_15=(19661847/1000000:ℚ); norm_num [lastCoefficient,Data.steps_15]
  · change lastCoefficient Data.steps_16=(19460727/1000000:ℚ); norm_num [lastCoefficient,Data.steps_16]
  · change lastCoefficient Data.steps_17=(19246411/1000000:ℚ); norm_num [lastCoefficient,Data.steps_17]
  · change lastCoefficient Data.steps_18=(19046871/1000000:ℚ); norm_num [lastCoefficient,Data.steps_18]
  · change lastCoefficient Data.steps_19=(2357563/125000:ℚ); norm_num [lastCoefficient,Data.steps_19]
  · change lastCoefficient Data.steps_20=(3737187/200000:ℚ); norm_num [lastCoefficient,Data.steps_20]
  · change lastCoefficient Data.steps_21=(18502173/1000000:ℚ); norm_num [lastCoefficient,Data.steps_21]
  · change lastCoefficient Data.steps_22=(1833039/100000:ℚ); norm_num [lastCoefficient,Data.steps_22]
  · change lastCoefficient Data.steps_23=(18169341/1000000:ℚ); norm_num [lastCoefficient,Data.steps_23]
  · change lastCoefficient Data.steps_24=(18017957/1000000:ℚ); norm_num [lastCoefficient,Data.steps_24]
  · change lastCoefficient Data.steps_25=(17859973/1000000:ℚ); norm_num [lastCoefficient,Data.steps_25]
  · change lastCoefficient Data.steps_26=(8855847/500000:ℚ); norm_num [lastCoefficient,Data.steps_26]
  · change lastCoefficient Data.steps_27=(17572177/1000000:ℚ); norm_num [lastCoefficient,Data.steps_27]
  · change lastCoefficient Data.steps_28=(17427861/1000000:ℚ); norm_num [lastCoefficient,Data.steps_28]
  · change lastCoefficient Data.steps_29=(8646109/500000:ℚ); norm_num [lastCoefficient,Data.steps_29]
  · change lastCoefficient Data.steps_30=(1072777/62500:ℚ); norm_num [lastCoefficient,Data.steps_30]
  · change lastCoefficient Data.steps_31=(8516577/500000:ℚ); norm_num [lastCoefficient,Data.steps_31]
  · change lastCoefficient Data.steps_32=(16909571/1000000:ℚ); norm_num [lastCoefficient,Data.steps_32]
  · change lastCoefficient Data.steps_33=(8396487/500000:ℚ); norm_num [lastCoefficient,Data.steps_33]
  · change lastCoefficient Data.steps_34=(16673827/1000000:ℚ); norm_num [lastCoefficient,Data.steps_34]
  · change lastCoefficient Data.steps_35=(4140367/250000:ℚ); norm_num [lastCoefficient,Data.steps_35]
  · change lastCoefficient Data.steps_36=(16455289/1000000:ℚ); norm_num [lastCoefficient,Data.steps_36]
  · change lastCoefficient Data.steps_37=(3269449/200000:ℚ); norm_num [lastCoefficient,Data.steps_37]
  · change lastCoefficient Data.steps_38=(16245163/1000000:ℚ); norm_num [lastCoefficient,Data.steps_38]
  · change lastCoefficient Data.steps_39=(16141829/1000000:ℚ); norm_num [lastCoefficient,Data.steps_39]
  · change lastCoefficient Data.steps_40=(4011047/250000:ℚ); norm_num [lastCoefficient,Data.steps_40]
  · change lastCoefficient Data.steps_41=(7972883/500000:ℚ); norm_num [lastCoefficient,Data.steps_41]
  · change lastCoefficient Data.steps_42=(15852741/1000000:ℚ); norm_num [lastCoefficient,Data.steps_42]
  · change lastCoefficient Data.steps_43=(3151859/200000:ℚ); norm_num [lastCoefficient,Data.steps_43]
  · change lastCoefficient Data.steps_44=(15670927/1000000:ℚ); norm_num [lastCoefficient,Data.steps_44]
  · change lastCoefficient Data.steps_45=(15582421/1000000:ℚ); norm_num [lastCoefficient,Data.steps_45]
  · change lastCoefficient Data.steps_46=(15498667/1000000:ℚ); norm_num [lastCoefficient,Data.steps_46]
  · change lastCoefficient Data.steps_47=(240859/15625:ℚ); norm_num [lastCoefficient,Data.steps_47]
  · change lastCoefficient Data.steps_48=(15335717/1000000:ℚ); norm_num [lastCoefficient,Data.steps_48]
  · change lastCoefficient Data.steps_49=(7628337/500000:ℚ); norm_num [lastCoefficient,Data.steps_49]
  · change lastCoefficient Data.steps_50=(3795439/250000:ℚ); norm_num [lastCoefficient,Data.steps_50]
  · change lastCoefficient Data.steps_51=(377679/25000:ℚ); norm_num [lastCoefficient,Data.steps_51]
  · change lastCoefficient Data.steps_52=(15033109/1000000:ℚ); norm_num [lastCoefficient,Data.steps_52]
  · change lastCoefficient Data.steps_53=(14962901/1000000:ℚ); norm_num [lastCoefficient,Data.steps_53]
  · change lastCoefficient Data.steps_54=(1861659/125000:ℚ); norm_num [lastCoefficient,Data.steps_54]
  · change lastCoefficient Data.steps_55=(231631/15625:ℚ); norm_num [lastCoefficient,Data.steps_55]
  · change lastCoefficient Data.steps_56=(1844879/125000:ℚ); norm_num [lastCoefficient,Data.steps_56]
  · change lastCoefficient Data.steps_57=(1836801/125000:ℚ); norm_num [lastCoefficient,Data.steps_57]
  · change lastCoefficient Data.steps_58=(3657657/250000:ℚ); norm_num [lastCoefficient,Data.steps_58]
  · change lastCoefficient Data.steps_59=(14567793/1000000:ℚ); norm_num [lastCoefficient,Data.steps_59]
  · change lastCoefficient Data.steps_60=(7254069/500000:ℚ); norm_num [lastCoefficient,Data.steps_60]
  · change lastCoefficient Data.steps_61=(14449361/1000000:ℚ); norm_num [lastCoefficient,Data.steps_61]
  · change lastCoefficient Data.steps_62=(7195767/500000:ℚ); norm_num [lastCoefficient,Data.steps_62]
  · change lastCoefficient Data.steps_63=(7167357/500000:ℚ); norm_num [lastCoefficient,Data.steps_63]
  · change lastCoefficient Data.steps_64=(14278949/1000000:ℚ); norm_num [lastCoefficient,Data.steps_64]
  · change lastCoefficient Data.steps_65=(3556069/250000:ℚ); norm_num [lastCoefficient,Data.steps_65]
  · change lastCoefficient Data.steps_66=(14170723/1000000:ℚ); norm_num [lastCoefficient,Data.steps_66]
  · change lastCoefficient Data.steps_67=(1411831/100000:ℚ); norm_num [lastCoefficient,Data.steps_67]
  · change lastCoefficient Data.steps_68=(14067049/1000000:ℚ); norm_num [lastCoefficient,Data.steps_68]
  · change lastCoefficient Data.steps_69=(2803389/200000:ℚ); norm_num [lastCoefficient,Data.steps_69]
  · change lastCoefficient Data.steps_70=(13967999/1000000:ℚ); norm_num [lastCoefficient,Data.steps_70]
  · change lastCoefficient Data.steps_71=(6960103/500000:ℚ); norm_num [lastCoefficient,Data.steps_71]
  · change lastCoefficient Data.steps_72=(13873559/1000000:ℚ); norm_num [lastCoefficient,Data.steps_72]
  · change lastCoefficient Data.steps_73=(13828047/1000000:ℚ); norm_num [lastCoefficient,Data.steps_73]
  · change lastCoefficient Data.steps_74=(13783653/1000000:ℚ); norm_num [lastCoefficient,Data.steps_74]
  · change lastCoefficient Data.steps_75=(6869679/500000:ℚ); norm_num [lastCoefficient,Data.steps_75]
  · change lastCoefficient Data.steps_76=(3424061/250000:ℚ); norm_num [lastCoefficient,Data.steps_76]
  · change lastCoefficient Data.steps_77=(13654281/1000000:ℚ); norm_num [lastCoefficient,Data.steps_77]
  · change lastCoefficient Data.steps_78=(13612577/1000000:ℚ); norm_num [lastCoefficient,Data.steps_78]
  · change lastCoefficient Data.steps_79=(848253/62500:ℚ); norm_num [lastCoefficient,Data.steps_79]
  · change lastCoefficient Data.steps_80=(13532659/1000000:ℚ); norm_num [lastCoefficient,Data.steps_80]
  · change lastCoefficient Data.steps_81=(6746813/500000:ℚ); norm_num [lastCoefficient,Data.steps_81]
  · change lastCoefficient Data.steps_82=(3363933/250000:ℚ); norm_num [lastCoefficient,Data.steps_82]
  · change lastCoefficient Data.steps_83=(13418257/1000000:ℚ); norm_num [lastCoefficient,Data.steps_83]
  · change lastCoefficient Data.steps_84=(13381259/1000000:ℚ); norm_num [lastCoefficient,Data.steps_84]
  · change lastCoefficient Data.steps_85=(13345399/1000000:ℚ); norm_num [lastCoefficient,Data.steps_85]
  · change lastCoefficient Data.steps_86=(2662009/200000:ℚ); norm_num [lastCoefficient,Data.steps_86]
  · change lastCoefficient Data.steps_87=(3318809/250000:ℚ); norm_num [lastCoefficient,Data.steps_87]
  · change lastCoefficient Data.steps_88=(6620501/500000:ℚ); norm_num [lastCoefficient,Data.steps_88]
  · change lastCoefficient Data.steps_89=(13207367/1000000:ℚ); norm_num [lastCoefficient,Data.steps_89]
  · change lastCoefficient Data.steps_90=(13174833/1000000:ℚ); norm_num [lastCoefficient,Data.steps_90]
  · change lastCoefficient Data.steps_91=(1642861/125000:ℚ); norm_num [lastCoefficient,Data.steps_91]
  · change lastCoefficient Data.steps_92=(1311111/100000:ℚ); norm_num [lastCoefficient,Data.steps_92]
  · change lastCoefficient Data.steps_93=(6539993/500000:ℚ); norm_num [lastCoefficient,Data.steps_93]
  · change lastCoefficient Data.steps_94=(163119/12500:ℚ); norm_num [lastCoefficient,Data.steps_94]
  · change lastCoefficient Data.steps_95=(6509857/500000:ℚ); norm_num [lastCoefficient,Data.steps_95]
  · change lastCoefficient Data.steps_96=(6495283/500000:ℚ); norm_num [lastCoefficient,Data.steps_96]
  · change lastCoefficient Data.steps_97=(12961729/1000000:ℚ); norm_num [lastCoefficient,Data.steps_97]
  · change lastCoefficient Data.steps_98=(12933573/1000000:ℚ); norm_num [lastCoefficient,Data.steps_98]
  · change lastCoefficient Data.steps_99=(516231/40000:ℚ); norm_num [lastCoefficient,Data.steps_99]
  · change lastCoefficient Data.steps_100=(12878667/1000000:ℚ); norm_num [lastCoefficient,Data.steps_100]
  · change lastCoefficient Data.steps_101=(12851949/1000000:ℚ); norm_num [lastCoefficient,Data.steps_101]
  · change lastCoefficient Data.steps_102=(801603/62500:ℚ); norm_num [lastCoefficient,Data.steps_102]
  · change lastCoefficient Data.steps_103=(6399891/500000:ℚ); norm_num [lastCoefficient,Data.steps_103]
  · change lastCoefficient Data.steps_104=(12774369/1000000:ℚ); norm_num [lastCoefficient,Data.steps_104]
  · change lastCoefficient Data.steps_105=(637471/50000:ℚ); norm_num [lastCoefficient,Data.steps_105]
  · change lastCoefficient Data.steps_106=(12724947/1000000:ℚ); norm_num [lastCoefficient,Data.steps_106]
  · change lastCoefficient Data.steps_107=(6350477/500000:ℚ); norm_num [lastCoefficient,Data.steps_107]
  · change lastCoefficient Data.steps_108=(12677447/1000000:ℚ); norm_num [lastCoefficient,Data.steps_108]
  · change lastCoefficient Data.steps_109=(6327117/500000:ℚ); norm_num [lastCoefficient,Data.steps_109]
  · change lastCoefficient Data.steps_110=(12631527/1000000:ℚ); norm_num [lastCoefficient,Data.steps_110]
  · change lastCoefficient Data.steps_111=(2521829/200000:ℚ); norm_num [lastCoefficient,Data.steps_111]
  · change lastCoefficient Data.steps_112=(12587277/1000000:ℚ); norm_num [lastCoefficient,Data.steps_112]
  · change lastCoefficient Data.steps_113=(12565757/1000000:ℚ); norm_num [lastCoefficient,Data.steps_113]
  · change lastCoefficient Data.steps_114=(12544597/1000000:ℚ); norm_num [lastCoefficient,Data.steps_114]
  · change lastCoefficient Data.steps_115=(12523811/1000000:ℚ); norm_num [lastCoefficient,Data.steps_115]
  · change lastCoefficient Data.steps_116=(2500681/200000:ℚ); norm_num [lastCoefficient,Data.steps_116]
  · change lastCoefficient Data.steps_117=(6241627/500000:ℚ); norm_num [lastCoefficient,Data.steps_117]
  · change lastCoefficient Data.steps_118=(12463507/1000000:ℚ); norm_num [lastCoefficient,Data.steps_118]
  · change lastCoefficient Data.steps_119=(2488809/200000:ℚ); norm_num [lastCoefficient,Data.steps_119]
  · change lastCoefficient Data.steps_120=(12424999/1000000:ℚ); norm_num [lastCoefficient,Data.steps_120]
  · change lastCoefficient Data.steps_121=(6203129/500000:ℚ); norm_num [lastCoefficient,Data.steps_121]
  · change lastCoefficient Data.steps_122=(1548479/125000:ℚ); norm_num [lastCoefficient,Data.steps_122]
  · change lastCoefficient Data.steps_123=(12369731/1000000:ℚ); norm_num [lastCoefficient,Data.steps_123]
  · change lastCoefficient Data.steps_124=(6175933/500000:ℚ); norm_num [lastCoefficient,Data.steps_124]
  · change lastCoefficient Data.steps_125=(12334347/1000000:ℚ); norm_num [lastCoefficient,Data.steps_125]
  · change lastCoefficient Data.steps_126=(12317089/1000000:ℚ); norm_num [lastCoefficient,Data.steps_126]
  · change lastCoefficient Data.steps_127=(12300189/1000000:ℚ); norm_num [lastCoefficient,Data.steps_127]
  · change lastCoefficient Data.steps_128=(2456713/200000:ℚ); norm_num [lastCoefficient,Data.steps_128]
  · change lastCoefficient Data.steps_129=(766697/62500:ℚ); norm_num [lastCoefficient,Data.steps_129]
  · change lastCoefficient Data.steps_130=(12251039/1000000:ℚ); norm_num [lastCoefficient,Data.steps_130]
  · change lastCoefficient Data.steps_131=(12235231/1000000:ℚ); norm_num [lastCoefficient,Data.steps_131]
  · change lastCoefficient Data.steps_132=(763729/62500:ℚ); norm_num [lastCoefficient,Data.steps_132]
  · change lastCoefficient Data.steps_133=(244087/20000:ℚ); norm_num [lastCoefficient,Data.steps_133]
  · change lastCoefficient Data.steps_134=(761831/62500:ℚ); norm_num [lastCoefficient,Data.steps_134]
  · change lastCoefficient Data.steps_135=(1217451/100000:ℚ); norm_num [lastCoefficient,Data.steps_135]
  · change lastCoefficient Data.steps_136=(12159941/1000000:ℚ); norm_num [lastCoefficient,Data.steps_136]
  · change lastCoefficient Data.steps_137=(7591/625:ℚ); norm_num [lastCoefficient,Data.steps_137]
  · change lastCoefficient Data.steps_138=(12131497/1000000:ℚ); norm_num [lastCoefficient,Data.steps_138]
  · change lastCoefficient Data.steps_139=(6058819/500000:ℚ); norm_num [lastCoefficient,Data.steps_139]
  · change lastCoefficient Data.steps_140=(12104029/1000000:ℚ); norm_num [lastCoefficient,Data.steps_140]

theorem small_budget : (∑ i : Fin 141,smallCoefficient i*smallMoment i) < (21/50:ℚ) := by decide +kernel
theorem cuts_length : cuts.length=142 := by decide +kernel
theorem small_cover {p : ℕ} (hp : 142<p) (hp1 : p≤10000) :
    ∃ i : Fin 141,smallLo i≤p ∧ p<smallHi i := by
  have hfirst : cuts.headD 0<p := by simpa only [cuts,List.headD_cons] using hp
  have hlast : p≤cuts.getLastD 0 := by simpa [cuts] using hp1
  obtain ⟨i,hi,hlo,hhi⟩ := adjacent_cover cuts p hfirst hlast
  have hib : i<141 := by rw [cuts_length] at hi; omega
  refine ⟨⟨i,hib⟩,?_,?_⟩
  · change cuts[i]!+1≤p; omega
  · change p<cuts[i+1]!+1; omega

end LonelyRunnerNew.LCNumeric.Index
