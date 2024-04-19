CartanMatrixAlgebra[g, {x, h, y}, {{2, -1}, {-1, 2}}]

SubAlgebra[u, g, Basis[g]]

UtoGsub = {u[i_] :> Image[u][[i]]};

brkTest = And@@Flatten[Table[VNormal[
	VPlus[Act[xx,yy]/.UtoGsub, 
		SVTimes[-1, Act[(xx/.UtoGsub), (yy/.UtoGsub)]]]]===0,
			{xx, Basis[u]}, {yy, Basis[u]}]];

Print[FullForm[brkTest]]

Test[
	Dim[g]
	,
	Dim[u]
	,
	TestID->"SubAlgebra-sl(2): Dims"
];

Test[
	brkTest
	,
	True
	,
	TestID->"SubAlgebra-sl(2): multiplication table"
];
	