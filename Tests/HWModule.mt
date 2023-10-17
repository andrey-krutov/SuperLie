CM = {{ 2, -1, -1},
	  {-1,  2,  0},
	  {-1,  0,  2}};

CartanMatrixAlgebra[g, {x,h,y}, CM]

Print[Dim[g]];

HWModule[v, g, {1, 0, 0}];

Print[Dim[v]];

testModStr = DeleteDuplicates[Flatten[Table[
	VNormal[Act[VNormal[Act[xx,yy]],vv] - Act[xx,VNormal[Act[yy,vv]]]] === 0,
	{xx, Basis[g]}, {yy,B Basis[g]}, {vv, Basis[v]}]]]


Test[
	testModStr
	,
	{True}
	,
	TestID->"HWModule: o(6), (1, 0, 0), table"
]
