Off[Solve::svars]

checkModule[aBasis_, mBasis_] :=
	DeleteDuplicates[Flatten[Table[
	VNormal[VPlus[Act[VNormal[Act[xx, yy]], vv], 
		SVTimes[-1, Act[xx, VNormal[Act[yy, vv]]]],  Act[yy, VNormal[Act[xx, vv]]]]] === 0,	
	{xx, aBasis}, {yy, aBasis}, {vv, mBasis}]]]  


CM = {{ 2, -1, -1},
	  {-1,  2,  0},
	  {-1,  0,  2}};

CartanMatrixAlgebra[g, {x,h,y}, CM]

HWModule[v1, g, {1, 0, 0}];
testv1 = checkModule[Basis[g], Basis[v1]]
dimv1 = Dim[v1]
 
HWModule[v2, g, {0, 1, 0}];
testv2 = checkModule[Basis[g], Basis[v2]]
dimv2 = Dim[v2]

HWModule[v3, g, {0, 0, 1}];
testv3 = checkModule[Basis[g], Basis[v3]]
dimv3 = Dim[v3]


Test[
	testv1
	,
	{True}
	,
	TestID->"HWModule: o(6), (1, 0, 0), table"
]
Test[
	dimv1
	,
	6
	,
	TestID->"HWModule: o(6), (1, 0, 0), Dim"
]
Test[
	testv2
	,
	{True}
	,
	TestID->"HWModule: o(6), (0, 1, 0), table"
]
Test[
	testv3
	,
	{True}
	,
	TestID->"HWModule: o(6), (0, 0, 1), table"
]



