Off[Solve::svars]


checkModule[aBasis_, mBasis_] :=
	DeleteDuplicates[Flatten[Table[
	VNormal[VPlus[Act[VNormal[Act[xx, yy]], vv], 
		SVTimes[-1, Act[xx, VNormal[Act[yy, vv]]]],  SVTimes[(-1)^(P[xx] P[yy]),Act[yy, VNormal[Act[xx, vv]]]]]] === 0,	
	{xx, aBasis}, {yy, aBasis}, {vv, mBasis}]]]  


CM = {{1}};

CartanMatrixAlgebra[g, {x,h,y}, CM, PList -> {1}]

For[i=1,i<10,++i,
	Clear[m];
	HWModule[m, g, {i}];
	testM = checkModule[Basis[g], Basis[m]];
	dimM = PDim[m];	

	Test[
		testM
		,
		{True}
		,
		TestID->StringForm["HWModule: osp(1|2), (``), table", i]
	];

	Test[
		dimM
		,
		{i+1,i}
		,
		TestID->StringForm["HWModule: osp(1|2), (``), dim", i]
	];
]


For[i=1,i<10,++i,
	Clear[m];
	HWModule[m, g, {i}, P->1];
	testM = checkModule[Basis[g], Basis[m]];
	dimM = PDim[m];	

	Test[
		testM
		,
		{True}
		,
		TestID->StringForm["HWModule: osp(1|2), Pi(``), table", i]
	];

	Test[
		dimM
		,
		{i,i+1}
		,
		TestID->StringForm["HWModule: osp(1|2), Pi(``), dim", i]
	];
]
