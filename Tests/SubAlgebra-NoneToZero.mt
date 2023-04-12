(* h(2n|2m) *)

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

HamiltonAlgebra[h, {p, \[Xi], \[Eta], q}]

basisUpToGrade = Flatten[Table[Basis[h, k], {k, -1, maxGrade}]];


SubAlgebra[u, h, basisUpToGrade, ToGrade -> maxGrade, 
 Grade -> (Deg[#, BasisPattern[h]] - 2 &)]
 
SubAlgebra[a, h, basisUpToGrade, ToGrade -> maxGrade, 
 Grade -> (Deg[#, BasisPattern[h]] - 2 &), NoneToZero -> True]
 
UtoGsub = {u[i_] :> Image[u][[i]]};
AtoGsub = {a[i_] :> Image[a][[i]]};
 
brkTableU = Flatten[Table[ VNormal[Act[xx,yy]/.UtoGsub], {xx, Basis[u]}, {yy, Basis[u]}]];
brkTableA = Flatten[Table[ VNormal[Act[xx,yy]/.AtoGsub], {xx, Basis[a]}, {yy, Basis[a]}]];
brkTableHupToGrade = Flatten[Table[VNormal[If[ Grade[xx]+Grade[yy]-4 > maxGrade, 0,
 	Hb[xx,yy]]], {xx, basisUpToGrade}, {yy, basisUpToGrade}]];
 
 
brkTestU = And@@Table[(brkTableU[[i]]/.{None->0}) === (brkTableHupToGrade[[i]]/.{None->0}),
 		 {i, Length[brkTableU]}];
 		 
brkTestA = And@@Table[brkTableA[[i]] === brkTableHupToGrade[[i]],
 		 {i, Length[brkTableU]}];
  		   
 Test[
	Dim[u]
	,
	Length[basisUpToGrade]
	,
	TestID->"SubAlgebra-UpToGrade: Dims"
];

 Test[
	brkTestU
	,
	True
	,
	TestID->"SubAlgebra-UpToGrade: Bracket (NoneToZero -> False)"
];

Test[
	brkTestA
	,
	True
	,
	TestID->"SubAlgebra-UpToGrade: Bracket (NoneToZero -> True)"
];
