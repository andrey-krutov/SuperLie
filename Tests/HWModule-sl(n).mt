Off[Solve::svars]

maxRank = 4;
maxSL2wgt = 10;

checkModule[aBasis_, mBasis_] :=
	DeleteDuplicates[Flatten[Table[
	VNormal[VPlus[Act[VNormal[Act[xx, yy]], vv], 
		SVTimes[-1, Act[xx, VNormal[Act[yy, vv]]]],  SVTimes[(-1)^(P[xx] P[yy]),Act[yy, VNormal[Act[xx, vv]]]]]] === 0,	
	{xx, aBasis}, {yy, aBasis}, {vv, mBasis}]]]  

CartanMatrixA[l_] := Table[-Delta[i-1,j] + 2 Delta[i,j] - Delta[i+1,j], {i,l}, {j,l}]

CartanMatrixAlgebra[g, {x,h,y}, CartanMatrixA[1], PList -> {0}]

For[i=1,i <= maxSL2wgt,++i,
	Clear[m];
	HWModule[m, g, {i}];
	testM = checkModule[Basis[g], Basis[m]];
	dimM = PDim[m];	

	Test[
		testM
		,
		{True}
		,
		TestID->StringForm["HWModule: sl(2), (``), table", i]
	];

	Test[
		dimM
		,
		{i+1,0}
		,
		TestID->StringForm["HWModule: sl(2), (``), dim", i]
	];
]



For[r=2,r <= maxRank, ++r,
	Print[StringForm["Testing: sl(``)", r+1]];;
	Clear[g];
	Clear[x];
	Clear[h];
	Clear[y];
	
	CartanMatrixAlgebra[g, {x,h,y}, CartanMatrixA[r]];

	For[i=1,i<5,++i,		
		Clear[m];
		wgt = Table[i Delta[k,1], {k,r}];
		Print[StringForm["Testing: sl(``) weight ``", r+1, wgt]];
		HWModule[m, g, wgt];
		testM = checkModule[Basis[g], Basis[m]];
		dimM = PDim[m];		
		
		Test[
			testM
			,
			{True}
			,
			TestID->StringForm["HWModule: sl(``), (``), table", r+1, wgt]
		];

		Test[
			dimM
			,
			{Binomial[r+i,i],0}
			,
			TestID->StringForm["HWModule: sl(``), (``), dim", r+1,wgt]
		];
	];
	
	For[i=2,i<r+1,++i,		
		Clear[m];
		wgt = Table[Delta[k,i], {k,r}];
		Print[StringForm["Testing: sl(``) weight ``", r+1, wgt]];
		HWModule[m, g, wgt];
		testM = checkModule[Basis[g], Basis[m]];
		dimM = PDim[m];		
		
		Test[
			testM
			,
			{True}
			,
			TestID->StringForm["HWModule: sl(``), (``), table", r+1, wgt]
		];

		Test[
			dimM
			,
			{Binomial[r+1,i],0}
			,
			TestID->StringForm["HWModule: sl(``), (``), dim", r+1,wgt]
		];
	];
	
		(* pi_p + pi_q *)
	wgts = Flatten[Table[{p, q}, {q, r}, {p, q, r}],1];

	Table[Module[{},	
		Clear[m];
		wgt = Table[Delta[k,w[[1]] ] + Delta[k,w[[2]] ], {k,r}];
		Print[StringForm["Testing: sl(``) weight ``", r+1, wgt]];
		HWModule[m, g, wgt];
		testM = checkModule[Basis[g], Basis[m]];
		dimM = PDim[m];		
		
		Test[
			testM
			,
			{True}
			,
			TestID->StringForm["HWModule: sl(``), (``), table", r+1, wgt]
		];

		Test[
			dimM
			,
			{(w[[1]]-w[[2]]+1)/(w[[1]]+1)Binomial[r+1,w[[1]]]Binomial[r+2,w[[2]]],0}
			,
			TestID->StringForm["HWModule: sl(``), (``), dim", r+1,wgt]
		];];
	, {w, wgts}];


]


