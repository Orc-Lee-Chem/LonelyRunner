import Mathlib.Data.Rat.Init

/- Frozen rational data. Proofs about these values are in Certificates. -/
namespace LonelyRunnerNew.Certificate
def Dbar : ℚ := 170685 / 1000
def Bbar : ℚ := 2137859 / 1000000
def Cbar : ℚ := 3004 / 1000000000
def tbar : ℚ := 1 - 2*Dbar/1375
def wbar : ℚ := 1699 / 10000
def edgebar : ℚ := 99984727 / 1000000
def sqrtHalfUpper : ℚ := 707107 / 1000000
structure PrimeRow where
  prime : ℕ
  tau : ℚ
  lambdaUpper : ℚ
  normUpper : ℚ
  edgeUpper : ℚ
  exponentNumerator : ℕ
  exponentDenominator : ℕ

def rows : List PrimeRow := [
  { prime := 2, tau := (37 / 201 : ℚ), lambdaUpper := (239039904683945577 / 250000000000000000 : ℚ), normUpper := (2052227387351 / 500000000000 : ℚ), edgeUpper := (7670990696489 / 1000000000000 : ℚ), exponentNumerator := 13, exponentDenominator := 201 },
  { prime := 3, tau := (347 / 2010 : ℚ), lambdaUpper := (229943863256961491 / 250000000000000000 : ℚ), normUpper := (3020875096473 / 1000000000000 : ℚ), edgeUpper := (640388639331 / 100000000000 : ℚ), exponentNumerator := 51, exponentDenominator := 670 },
  { prime := 5, tau := (107 / 670 : ℚ), lambdaUpper := (433234887172698753 / 500000000000000000 : ℚ), normUpper := (1165676003063 / 500000000000 : ℚ), edgeUpper := (662523832733 / 125000000000 : ℚ), exponentNumerator := 179, exponentDenominator := 2010 },
  { prime := 7, tau := (61 / 402 : ℚ), lambdaUpper := (827966712339599119 / 1000000000000000000 : ℚ), normUpper := (512534882139 / 250000000000 : ℚ), edgeUpper := (2365565222337 / 500000000000 : ℚ), exponentNumerator := 13, exponentDenominator := 134 },
  { prime := 11, tau := (142 / 1005 : ℚ), lambdaUpper := (386419601781774073 / 500000000000000000 : ℚ), normUpper := (1782326207659 / 1000000000000 : ℚ), edgeUpper := (4090203987259 / 1000000000000 : ℚ), exponentNumerator := 36, exponentDenominator := 335 },
  { prime := 13, tau := (277 / 2010 : ℚ), lambdaUpper := (752338436064506727 / 1000000000000000000 : ℚ), normUpper := (426782995477 / 250000000000 : ℚ), edgeUpper := (155231431817 / 40000000000 : ℚ), exponentNumerator := 223, exponentDenominator := 2010 },
  { prime := 17, tau := (133 / 1005 : ℚ), lambdaUpper := (719041087633262413 / 1000000000000000000 : ℚ), normUpper := (400970308931 / 250000000000 : ℚ), edgeUpper := (3569839071111 / 1000000000000 : ℚ), exponentNumerator := 39, exponentDenominator := 335 },
  { prime := 19, tau := (131 / 1005 : ℚ), lambdaUpper := (352821789895820887 / 500000000000000000 : ℚ), normUpper := (1567671179159 / 1000000000000 : ℚ), edgeUpper := (1724576903557 / 500000000000 : ℚ), exponentNumerator := 119, exponentDenominator := 1005 },
  { prime := 23, tau := (17 / 134 : ℚ), lambdaUpper := (27294694651410319 / 40000000000000000 : ℚ), normUpper := (47209502951 / 31250000000 : ℚ), edgeUpper := (3252068305893 / 1000000000000 : ℚ), exponentNumerator := 49, exponentDenominator := 402 },
  { prime := 29, tau := (41 / 335 : ℚ), lambdaUpper := (653430582635210863 / 1000000000000000000 : ℚ), normUpper := (724374486917 / 500000000000 : ℚ), edgeUpper := (151444678617 / 50000000000 : ℚ), exponentNumerator := 127, exponentDenominator := 1005 },
  { prime := 31, tau := (122 / 1005 : ℚ), lambdaUpper := (645736634762783613 / 1000000000000000000 : ℚ), normUpper := (1433699936691 / 1000000000000 : ℚ), edgeUpper := (2967702979251 / 1000000000000 : ℚ), exponentNumerator := 128, exponentDenominator := 1005 },
  { prime := 37, tau := (119 / 1005 : ℚ), lambdaUpper := (312289685490954997 / 500000000000000000 : ℚ), normUpper := (697506887943 / 500000000000 : ℚ), edgeUpper := (2811502620707 / 1000000000000 : ℚ), exponentNumerator := 131, exponentDenominator := 1005 },
  { prime := 41, tau := (39 / 335 : ℚ), lambdaUpper := (611740047529935547 / 1000000000000000000 : ℚ), normUpper := (686648751691 / 500000000000 : ℚ), edgeUpper := (681198415611 / 250000000000 : ℚ), exponentNumerator := 133, exponentDenominator := 1005 },
  { prime := 43, tau := (233 / 2010 : ℚ), lambdaUpper := (606759907977679439 / 1000000000000000000 : ℚ), normUpper := (273040710223 / 200000000000 : ℚ), edgeUpper := (671373512687 / 250000000000 : ℚ), exponentNumerator := 89, exponentDenominator := 670 },
  { prime := 47, tau := (23 / 201 : ℚ), lambdaUpper := (596197073582320963 / 1000000000000000000 : ℚ), normUpper := (269722296193 / 200000000000 : ℚ), edgeUpper := (1306830035577 / 500000000000 : ℚ), exponentNumerator := 9, exponentDenominator := 67 },
  { prime := 53, tau := (113 / 1005 : ℚ), lambdaUpper := (145508869725981853 / 250000000000000000 : ℚ), normUpper := (265504705137 / 200000000000 : ℚ), edgeUpper := (314968774063 / 125000000000 : ℚ), exponentNumerator := 137, exponentDenominator := 1005 },
  { prime := 59, tau := (223 / 2010 : ℚ), lambdaUpper := (570108098562518013 / 1000000000000000000 : ℚ), normUpper := (655360565893 / 500000000000 : ℚ), edgeUpper := (2438837267921 / 1000000000000 : ℚ), exponentNumerator := 277, exponentDenominator := 2010 },
  { prime := 61, tau := (37 / 335 : ℚ), lambdaUpper := (566335497851137739 / 1000000000000000000 : ℚ), normUpper := (1305579132731 / 1000000000000 : ℚ), edgeUpper := (603558459043 / 250000000000 : ℚ), exponentNumerator := 139, exponentDenominator := 1005 },
  { prime := 67, tau := (22 / 201 : ℚ), lambdaUpper := (278350127680116823 / 500000000000000000 : ℚ), normUpper := (5050023167 / 3906250000 : ℚ), edgeUpper := (117317759673 / 50000000000 : ℚ), exponentNumerator := 28, exponentDenominator := 201 },
  { prime := 71, tau := (109 / 1005 : ℚ), lambdaUpper := (549884169117320227 / 1000000000000000000 : ℚ), normUpper := (25681422043 / 20000000000 : ℚ), edgeUpper := (230537391869 / 100000000000 : ℚ), exponentNumerator := 47, exponentDenominator := 335 },
  { prime := 73, tau := (217 / 2010 : ℚ), lambdaUpper := (546577257884660917 / 1000000000000000000 : ℚ), normUpper := (1279920129399 / 1000000000000 : ℚ), edgeUpper := (285750766663 / 125000000000 : ℚ), exponentNumerator := 283, exponentDenominator := 2010 },
  { prime := 79, tau := (43 / 402 : ℚ), lambdaUpper := (269093666696575373 / 500000000000000000 : ℚ), normUpper := (1269635417813 / 1000000000000 : ℚ), edgeUpper := (223184591259 / 100000000000 : ℚ), exponentNumerator := 19, exponentDenominator := 134 },
  { prime := 83, tau := (107 / 1005 : ℚ), lambdaUpper := (266628857288836303 / 500000000000000000 : ℚ), normUpper := (252750599181 / 200000000000 : ℚ), edgeUpper := (2198656928103 / 1000000000000 : ℚ), exponentNumerator := 143, exponentDenominator := 1005 },
  { prime := 89, tau := (106 / 1005 : ℚ), lambdaUpper := (131408792801539733 / 250000000000000000 : ℚ), normUpper := (1254883102039 / 1000000000000 : ℚ), edgeUpper := (2152619194079 / 1000000000000 : ℚ), exponentNumerator := 48, exponentDenominator := 335 },
  { prime := 97, tau := (7 / 67 : ℚ), lambdaUpper := (103366863256090969 / 200000000000000000 : ℚ), normUpper := (124497185083 / 100000000000 : ℚ), edgeUpper := (1048611830883 / 500000000000 : ℚ), exponentNumerator := 29, exponentDenominator := 201 },
  { prime := 101, tau := (209 / 2010 : ℚ), lambdaUpper := (512651378446270799 / 1000000000000000000 : ℚ), normUpper := (15504763437 / 12500000000 : ℚ), edgeUpper := (258966201167 / 125000000000 : ℚ), exponentNumerator := 97, exponentDenominator := 670 },
  { prime := 103, tau := (104 / 1005 : ℚ), lambdaUpper := (255010363549774991 / 500000000000000000 : ℚ), normUpper := (1237532556133 / 1000000000000 : ℚ), edgeUpper := (1029736157291 / 500000000000 : ℚ), exponentNumerator := 146, exponentDenominator := 1005 },
  { prime := 107, tau := (69 / 670 : ℚ), lambdaUpper := (253013916262421713 / 500000000000000000 : ℚ), normUpper := (246653004217 / 200000000000 : ℚ), edgeUpper := (2035878906713 / 1000000000000 : ℚ), exponentNumerator := 293, exponentDenominator := 2010 },
  { prime := 109, tau := (69 / 670 : ℚ), lambdaUpper := (126165907732453833 / 250000000000000000 : ℚ), normUpper := (246364457227 / 200000000000 : ℚ), edgeUpper := (2024512845143 / 1000000000000 : ℚ), exponentNumerator := 293, exponentDenominator := 2010 },
  { prime := 113, tau := (103 / 1005 : ℚ), lambdaUpper := (125209990504171513 / 250000000000000000 : ℚ), normUpper := (613909726887 / 500000000000 : ℚ), edgeUpper := (2002582458967 / 1000000000000 : ℚ), exponentNumerator := 49, exponentDenominator := 335 },
  { prime := 127, tau := (203 / 2010 : ℚ), lambdaUpper := (488809288816073857 / 1000000000000000000 : ℚ), normUpper := (24312178349 / 20000000000 : ℚ), edgeUpper := (483303801639 / 250000000000 : ℚ), exponentNumerator := 99, exponentDenominator := 670 },
  { prime := 131, tau := (101 / 1005 : ℚ), lambdaUpper := (97079178393809873 / 200000000000000000 : ℚ), normUpper := (48489904621 / 40000000000 : ℚ), edgeUpper := (957616588461 / 500000000000 : ℚ), exponentNumerator := 149, exponentDenominator := 1005 },
  { prime := 137, tau := (1 / 10 : ℚ), lambdaUpper := (481004929920833069 / 1000000000000000000 : ℚ), normUpper := (1207988805489 / 1000000000000 : ℚ), edgeUpper := (188956832491 / 100000000000 : ℚ), exponentNumerator := 299, exponentDenominator := 2010 },
  { prime := 139, tau := (1 / 10 : ℚ), lambdaUpper := (95993807287752553 / 200000000000000000 : ℚ), normUpper := (48279785617 / 40000000000 : ℚ), edgeUpper := (734896491 / 390625000 : ℚ), exponentNumerator := 299, exponentDenominator := 2010 }
]
def realLambdaUpper : ℚ := (841621684286490159 / 1000000000000000000 : ℚ)
end LonelyRunnerNew.Certificate
