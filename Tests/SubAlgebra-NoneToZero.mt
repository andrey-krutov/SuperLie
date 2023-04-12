(* h(2n|2m) *)

Off[Solve::svars]

n = 1
m = 1
maxGrade = 2

VectorSpace[p, Dim -> {n, 0}]
VectorSpace[q, Dim -> {n, 0}]
VectorSpace[\[Xi], Dim -> {0, m}]
VectorSpace[\[Eta], Dim -> {0, m}]

Grade[p[i_]] := 1
Grade[q[j_]] := 1
Grade[\[Xi][i_]] := 1
Grade[\[Eta][i_]] := 1

Symmetric[VTimes]

HamiltonAlgebra[h, {p, \[Eta], \[Xi], q}]

basisUpToGrade = Flatten[Table[Basis[h, k], {k, -1, maxGrade}]];

$DPrint = 1
SubAlgebra[u, h, basisUpToGrade, ToGrade -> maxGrade, 
 Grade -> (Deg[#, BasisPattern[h]] - 2 &)]
$DPrint = 0

Test[
	Dim[u]
	,
	Length[basisUpToGrade]
	,
	TestID -> "The dimension of the sublagebra of h(2|2) with UpToGrade option"
]
