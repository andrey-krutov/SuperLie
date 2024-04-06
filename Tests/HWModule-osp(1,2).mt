Off[Solve::svars]


checkModule[aBasis_, mBasis_] :=
	DeleteDuplicates[Flatten[Table[
	VNormal[VPlus[Act[VNormal[Act[xx, yy]], vv], 
		SVTimes[-1, Act[xx, VNormal[Act[yy, vv]]]],  SVTimes[(-1)^(P[xx] P[yy]),Act[yy, VNormal[Act[xx, vv]]]]]] === 0,	
	{xx, aBasis}, {yy, aBasis}, {vv, mBasis}]]]  


CM = {{1}};

CartanMatrixAlgebra[g, {x,h,y}, CM, PList -> {1}]

HWModule[v1, g, {1}];
testv1 = checkModule[Basis[g], Basis[v1]]
dimv1 = PDim[v1]
 
HWModule[v2, g, {2}];
testv2 = checkModule[Basis[g], Basis[v2]]
dimv2 = PDim[v2]

HWModule[v3, g, {3}];
testv3 = checkModule[Basis[g], Basis[v3]]
dimv3 = PDim[v3]


Test[
	testv1
	,
	{True}
	,
	TestID->"HWModule: osp(1|2), (1), table"
]

Test[
	dimv1
	,
	{2,1}
	,
	TestID->"HWModule: osp(1|2), (1), Dim"
]

Test[
	testv2
	,
	{True}
	,
	TestID->"HWModule: osp(1|2), (2), table"
]

Test[
	dimv2
	,
	{3,2}
	,
	TestID->"HWModule: osp(1|2), (2), Dim"
]


Test[
	testv3
	,
	{True}
	,
	TestID->"HWModule: osp(1|2), (3), table"
]

Test[
	dimv3
	,
	{4,3}
	,
	TestID->"HWModule: osp(1|2), (3), Dim"
]
