Off[Solve::svars]

checkModule[aBasis_, mBasis_] :=
	DeleteDuplicates[Flatten[Table[
	VNormal[VPlus[Act[VNormal[Act[xx, yy]], vv], 
		SVTimes[-1, Act[xx, VNormal[Act[yy, vv]]]],  SVTimes[(-1)^(P[xx] P[yy]),Act[yy, VNormal[Act[xx, vv]]]]]] === 0,	
	{xx, aBasis}, {yy, aBasis}, {vv, mBasis}]]]  


CM = {{0, 1},
	  {-1, 0}};

CartanMatrixAlgebra[g, {x,h,y}, CM, PList -> {1,1}]


HWModule[v1, g, {1, 0}];
testv1 = checkModule[Basis[g], Basis[v1]]
dimv1 = PDim[v1]
 
HWModule[v2, g, {2, 0}];
testv2 = checkModule[Basis[g], Basis[v2]]
dimv2 = PDim[v2]

HWModule[v3, g, {3, 0}];
testv3 = checkModule[Basis[g], Basis[v3]]
dimv3 = PDim[v3]


Test[
	testv1
	,
	{True}
	,
	TestID->"HWModule: sl(1|1), (1, 0), table"
]

Test[
	dimv1
	,
	{2,1}
	,
	TestID->"HWModule: sl(1|1), (1, 0), Dim"
]

Test[
	testv2
	,
	{True}
	,
	TestID->"HWModule: sl(1|1), (0, 1), table"
]

Test[
	testv3
	,
	{True}
	,
	TestID->"HWModule: sl(1|1), (1, 1), table"
]

