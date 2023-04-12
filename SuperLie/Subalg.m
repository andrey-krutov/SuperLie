BeginPackage["SuperLie`Subalg`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`",
  "SuperLie`Space`", "SuperLie`Generate`", "SuperLie`Vsplit`"}]

SuperLie`Subalg`SubAlgebra::usage =
 "SubAlgebra[sub,alg,{gen}] - defines the subalgebra \"sub\" of the Lie
(super)algebra \"alg\", generated by elements \"gen\".";

SuperLie`Subalg`AlgebraDecomposition::usage =
 "AlgebraDecomposition[alg,{sub1->{g11,...}, ...}] - defines the subalgebras
 sub1, ... of the Lie (super)algebra alg, generated by elements g11, ...
 The algeba alg must be equal to the sum of the components."

SuperLie`Subalg`DefSubAlgebra::usage = 
 "DefSubAlgebra[sub, alg, {gen,..}] - defines the subalgebra \"sub\" of the Lie
 (super)algebra \"alg\", generated by elements \"gen\".";

Split

Begin["$`"]

(* --------- SubAlgebra ------------------------------------------ #)
>
>	Builds a subalgebra from the list of generators 
>
>   Arguments:
>	g   - the name of the new algebra
>	in  - the name of the old algebra
>	elt - the list of generators in the form {value, ..} or
>             {name->value, ... }
>   Options:
>	ToDegree->rn  - maximal degree of basis and relations in terms of
>                       generators (default - Infinity)
>	Grade->fn  - grading conversion function. The grading of element
>		      x in g is equal to fn[image[x]]. Default is Grade.
>	ToGrade->rn - compute up to the grade rn. The Grade function
>		      must be defined.
>	Grade->{fn,rn}   - compute up to the grade rn. Use fn as grading
>                      function (obsolete).
>	GList->{g1,...}  - provides grades for generators. Not compatible
>			with Grade->fn. 
>	Weight->fn  - weight conversion function. The weight of element
>		      x in g is equal to fn[image[x]]. Default is Weight.
>   Results:
>	Act[g[i],g[j]] - the bracket in new algebra
>	GenBasis[g] - the basis of "g" in term of generators
>	GenRel[g] - the list of relations between generators
>	Image[g] - the basis of "g" in containing algebra
>	Dim[g] - the dimension of "g" (or of evaluated part of "g")
>	PDim[g] - the (even|odd) dimension of "g"
>	BasisPattern[g] - the pattern for basis elements of "g"
>	ToDegree[g] - equal to input option ToDegree
>	Grade[g[i]] - the degree of GenBasis[g][[i]]. If all relations are
>		homogeneous, this is the grading of "g". Not redefined
>		with option Grade->rn
>
(# --------------------------------------------------------------- *)

SubAlgebra::par = "No parity of `` defined. Assumed 0."
SubAlgebra::nograde = "Unable to calculate the grading of generators. Grade restriction ignored" 
(*SubAlgebra::pmgen = "The gradings of generators have different signs. Grade restriction ignored."*)
SubAlgebra::pmgen = "The gradings of generators have different signs. Grade restriction may result in loss of sertain elements."
SubAlgebra::mixgrade = "The generators are not graded"
 
SubAlgebra[g_, in_, elt_List, opts___Rule] :=
  Module[{ gen, zv, dim, y, r, q, s, t, i, j, l, sm, brk, Brk, inBrk, sqr,
		agl, pgl, gt, pgt, bs, tog, eq, yQ, z, zg, vars, solj, sv, glist,
		rel={}, jac, prev, gentbl, hl, rn, pg, pin, wt, props, grade$fn, gg,
		none2zero},
$tm = TimeUsed[];
	Clear["$`gen$*"];
    If [(Clear /. {opts}) =!= False, Clear[g]];
    rn = ToDegree /. {opts} /. ToDegree->Infinity;
    Brk = Bracket /. {opts} /. Bracket->Act;
    brk = bracket /. {opts} /. bracket->act;    
    none2zero = NoneToZero /. {opts} /. NoneToZero->False;    
    inBrk = Bracket[in];
    wt = Weight /. {opts};
    glist = GList /. {opts} /. GList->Auto;
    If[NumberQ[glist],glist=Table[glist,{Length[elt]}]];
    grade$fn = Grade /. {opts, Grade->Auto};
	Which [
	  ListQ[grade$fn],
	    gg=grade$fn[[2]];
	    grade$fn = grade$fn[[1]],
	  NumberQ[grade$fn],
	    gg=grade$fn;
	    grade$fn = Auto,
	  True,
	    gg=Infinity
	];
    maxGrade$ = ToGrade /. {opts} /. ToGrade->gg;
    If[grade$fn===Auto,
      grade$fn = Grade;
      If[glist===Auto,
        glist = TestGrade /@ elt;
        If[MemberQ[glist, Mixed],
          Message[SubAlgebra::mixgrade];
          grade$fn = (0&);
          glist = Auto]]];
    Vector[g, y];
    Relatives[g] ^= Prepend[Table[None, {7}], g];
    If[!NumberQ[P[Brk]],
      Message[SubAlgebra::par, Brk]];
    If[inBrk=!=Brk && !NumberQ[P[inBrk]], 
      Message[SubAlgebra::par, inBrk]];
    pg = If[OddQ[P[Brk]], 1, 0];
    pin = If[OddQ[P[Bracket[in]]], 1, 0];
	If[pg==1, Message[SubAlgebra::odd, Brk]; Return[$Failed]];
    dim = Length[elt];		           (* number of elements *)
    If [elt[[1,0]]===Rule,
      {gen$basis, zv} =
	 Transpose @ Apply[List, elt, {1}], (* names and values of elt *)
    (* else *)
      zv = elt;
      gen$basis = Array[g, dim]
    ];
	
	gg = grade$fn /@ zv;
	Which [
	  Select[gg, !NumberQ[#]&, 1]=!={},
		If[NumberQ[maxGrade$],
		  Message[SubAlgebra::nograde];
		  maxGrade$ = Infinity],
	  Not[Equal @@ gg] || (NumberQ[maxGrade$] && (Min @@ gg) <0),
	    If [(Min @@ gg) <0 && (Max @@ gg) >0 ,
		  If[NumberQ[maxGrade$],
		    Message[SubAlgebra::pmgen](*;maxGrade$ = Infinity*)],
		(* else *)
	      Return[GradedSubAlgebra[g, in, elt, opts]]]	   (* Use version for grade subalgebra *)
	];
    gen$par = P /@ zv;			   (* list of parities *)
    gen$super = MemberQ[gen$par,1-pin];
    If [gen$super,
      If[pg!=pin, gen$par=1-gen$par];
      P[g[i$_]] ^:= gen$par[[i$]],
	(*else*)   P[_g] ^= pg
    ];

(* The conversion to {g[i]} basis *)
    bs = BasisPattern[in];				(* basis pattern *)
    tog = VSolve[ Table[zv[[i]]==g[i], {i,dim}], MatchList[zv, bs] ] [[1]];
   DPrint[3, "bs=", bs, ", tog: ", tog];
(* Lie operation in terms of generators *)

   gentbl := gen$tbl;
   sqr = Squaring/.{opts}/.Squaring:>($p===2);
   If [sqr,
     gensqr := gen$sqr;
     TableBracket[g, Brk, Unevaluated[gentbl], brk, Infinity, Unevaluated[gensqr]],
   (* else *)
     TableBracket[g, Brk, Unevaluated[gentbl], brk, Infinity]
   ];
   Grade[g[i_]] ^:= GList[g][[i]];
   Weight[g[i_]] ^:= WList[g][[i]];

(*   ActTable[g] ^:= VNormal[gen$tbl]; *)
   NGen[g] ^= dim;
   gen$deg = Table[1, {dim}];
   gen$rel = gen$tbl = gen$sqr = par = {};
   gen$ind = {1, dim+1};
   gen$rng = 1;
   gen$prev = Table[0, {dim}];	(* precedence list for Holl basis *)
   $tm = TimeUsed[]; (* timer *)
   For [r=2, r<=rn, ++r,	(*  r = current degree *)
    DPrint[1, "start loop ", r, "  (", N[TimeUsed[ ]-$tm,4]," sec)" ]; $tm = TimeUsed[];
    If [r>2*gen$rng, Break[]];
    If[NumberQ[maxGrade$],
     GList[g] ^= If[glist===Auto, grade$fn /@ zv, calcGList[GenBasis[g],glist]]];
    npairs = StepGeneration[g, r, rn, Brk, brk, sqr];
(* Distribute the remaining gen$var[hl,i] among the basis and the relations *)
    For [ i=1, i<=npairs, ++i,
	 If [ gen$flag[[i]], Continue[] ];		(* y[i] was removed *)
	 z = gen$lst[[i]] /. { brk->Bracket[in], g[k_]:>zv[[k]] }; (* image *)
     z = VNormal[z];
	 zg = VNormal[ LinearChange[z, tog] ];	(* in {g} basis *)
	 vars = MatchList[zg, bs];		(* remaining old basis *)
     DPrint[3, "gen$lst[[",i,"]]=",gen$lst[[i]], ", z=",z, ", zg=",zg, ", vars=",vars];
	 If [vars==={},				(* no old ==> relation *)
	    gen$rel = Append[gen$rel, gen$lst[[i]]==zg];
	    gen$var[_,i] = zg,			(* in {g} basis *)
	 (*else*)				(* add to {g} basis *)
	    gen$basis = {gen$basis, gen$lst[[i]]};  (* generation list *)
	    AppendTo[ zv, z ];			     (* image list *)
	    If [gen$super, par = {par, P[ gen$lst[[i]] ]} ];
	    gen$prev = {gen$prev, gen$lst[[i,1,1]]};	  (* Hall basis list *)
	    sv = VSolve[ zg==g[++dim], vars][[1]]; 
	    tog = Map[VNormal, Join[ LinearChange[tog,sv], sv ], {2}];
	    gen$var[_,i] = g[dim]
	 ]
    ];
    DPrint[1, "distribute -> ", N[TimeUsed[ ]-$tm,4], " sec" ]; $tm = TimeUsed[];
    gen$tbl = gen$tbl//.RestoreSV;		(* replace all gen$var[i] *)
    If [sqr, gen$sqr = gen$sqr//.RestoreSV];	(* replace all gen$var[i] *)
(*      Clear[gen$var];
        VectorQ[gen$var]^=True; *)
    AppendTo[gen$ind, dim+1];
    rdim = gen$ind[[-1]] - gen$ind[[-2]];
    If [rdim>0,
	  gen$rng = r;
	  gen$deg = Join[gen$deg, Table[r, {rdim}]]; 
      gen$prev = Flatten[gen$prev];
    ];
    If [gen$super,
	  par = Flatten[par];
	  If[pg!=pin, par = 1 - par];
	  gen$par = Join[gen$par, par];
	  par = {};
      l = Plus @@ gen$par;
      DPrint[1, "r = ", r,  ", Dim = (", dim-l, "|", l, ")" ],
    (*else*)
	  DPrint[1, "r = ", r,  ", Dim = ", dim]
    ];
    gen$basis = Flatten[gen$basis];
    GenBasis[g] ^=  gen$basis //. g[i_] :> gen$basis[[i]];
    GenRel[g] ^= gen$rel //. g[i_] :> gen$basis[[i]];
    DPrint[2, GenRel[g] ];
   ];
   (* Final assignment *)   
   If[none2zero, 
     gen$tbl = gen$tbl /. {None -> 0};
     If[sqr, 
     	gen$sqr = gen$sqr /. {None -> 0};
     ];
   ];
   ActTable[g] ^= VNormal[gen$tbl];   
   If[sqr,
     SqrTable[g] ^= VNormal[gen$sqr];
     TableBracket[g, Brk, Unevaluated[ActTable[g]], brk, rn, Unevaluated[SqrTable[g]]],
   (* else *)
     TableBracket[g, Brk, Unevaluated[ActTable[g]], brk, rn]
   ];
   ToDegree[g] ^= rn;
   ToGrade[g] ^= maxGrade$;
   RangeIndex[g] ^= gen$ind;
   gen$basis = Flatten[gen$basis];
   GenBasis[g] ^=  gen$basis //. g[i_] :> gen$basis[[i]];
   GenRel[g] ^= gen$rel //. g[i_] :> gen$basis[[i]];
   With[{brk=Bracket[in], bs = BasisPattern[in]},
	g/: Brk[g[i_], y:bs] := brk[Image[g][[i]], y]];
(*    JacRel[g] ^= jrel; *)
   props = ComplementKeys[{opts}, {Clear, Grade, Weight}];
   SubSpace[g, in, zv, Clear->False, Hold[PiOrder]->(pg!=pin), Sequence@@props];
   DPrint[1, StringForm["Dim[``] = ", g], FDim[g] ];
   Clear["$`gen$*"];
   Bracket[g] ^= Brk;
   BracketMode[g] ^= Tabular;
   TheAlgebra[g] ^= g;
   TheModule[g[_]] ^= g; 
   GList[g] ^= If[glist===Auto, grade$fn /@ Image[g], calcGList[GenBasis[g],glist]];
   maxGrade$=.;
   WList[g] ^= wt /@ Image[g];
   g::usage = SPrint["`` is a sublagebra in ``", g, in]
]


calcGList[ex_List, glist_List] := 
  Module[{x, n = Length[glist]},
  (Deg /@ (ex /. Table[ex[[i]] -> x[i], {i, n}])) /. 
      Table[Deg[x[i]] -> glist[[i]], {i, n}]]


(* Variant for graded algebra *)


GradedSubAlgebra[g_, in_, elt_List, opts___Rule] :=
  Module[{ gen, zv, dim, y, r, q, s, t, i, j, l, sm, brk, Brk, inBrk, sqr,
		agl, pgl, gt, pgt, bs, tog, eq, yQ, z, zg, vars, solj, sv, glist,
		rel={}, jac, prev, gentbl, gensqr, hl, rn, pg, pin, wt, props, grade$fn,
		grgen, grmin, grmax, grsign=1, gnames, gvalues, ngen, dPrev, dm, ri, gpos},
$tm = TimeUsed[];
	Clear["$`gen$*"];
    bs = BasisPattern[in];				(* basis pattern *)
    If [(Clear /. {opts}) =!= False, Clear[g]];
    rn = ToDegree /. {opts} /. ToDegree->Infinity;
    Brk = Bracket /. {opts} /. Bracket->Act;
    brk = bracket /. {opts} /. bracket->act;
    inBrk = Bracket[in];
    wt = Weight /. {opts};
    glist = GList /. {opts} /. GList->Auto;
    If[NumberQ[glist],glist=Table[glist,{Length[elt]}]];
    grade$fn = Grade /. {opts};
	Which [
	  ListQ[grade$fn],
	    grmax=grade$fn[[2]];
	    grade$fn = grade$fn[[1]],
	  NumberQ[grade$fn],
	    grmax=grade$fn;
	    grade$fn = Grade,
	  True,
	    grmax=Infinity
	];
    maxGrade$ = ToGrade /. {opts} /. ToGrade->grmax;
    Vector[g, y];
    Relatives[g] ^= Prepend[Table[None, {7}], g];
    If[!NumberQ[P[Brk]],
      Message[SubAlgebra::par, Brk]];
    If[inBrk=!=Brk && !NumberQ[P[inBrk]], 
      Message[SubAlgebra::par, inBrk]];
    pg = If[OddQ[P[Brk]], 1, 0];
    pin = If[OddQ[P[Bracket[in]]], 1, 0];
	If[pg==1, Message[SubAlgebra::odd, Brk]; Return[$Failed]];
    ngen = Length[elt];		           (* number of elements *)
    If [elt[[1,0]]===Rule,
      {gnames, gvalues} =
	     Transpose @ Apply[List, elt, {1}], (* names and values of elt *)
    (* else *)
      gvalues = elt;
      gnames = False
    ];
	grgen = grade$fn /@ gvalues;  (* grades of generators *)
	grmin = Min @@ grgen;
	grmax = Max @@ grgen;
	If [grmin<0,
	  If [grmax>0,
	    Message["SubAlgebra::pmgen"];
		Return[SubAlgebra[g, in, elt, Grade->grade$fn, opts]],
	  (*else*)
	    grsign = -1;
		{grmin,grmax} = - {grmax,grmin}]];
    gen$par = P /@ gvalues;			   (* list of parities *)
    gen$super = MemberQ[gen$par,1-pin];
    If [gen$super,
      If[pg!=pin, gen$par=1-gen$par];
      P[g[i$_]] ^:= gen$par[[i$]],
	(*else*)   P[_g] ^= pg
    ];
	gr$min = grmin;
    DPrint[1, "Grades of generators: ", grgen, ", min: ", grmin, ", max: ", grmax,
     ", calc up to grade ", maxGrade$, " and degree ", rn];

(* Lie operation in terms of generators *)

    gentbl := gen$tbl;
    sqr = Squaring/.{opts}/.Squaring:>($p===2);
    If [sqr,
      gensqr := gen$sqr;
      TableBracket[g, Brk, Unevaluated[gentbl], brk, Infinity, Unevaluated[gensqr]],
    (* else *)
      TableBracket[g, Brk, Unevaluated[gentbl], brk, Infinity]
    ];
    Grade[g[i_]] ^:= GList[g][[i]];
    Weight[g[i_]] ^:= WList[g][[i]];
    NGen[g] ^= ngen;

    gen$deg = {};  (* not used? *)
    gen$rel = gen$tbl = gen$sqr = gen$par = par = {};
    Clear[gen$rng];
    gen$rng[] = grmax;
    gen$prev = {};	(* precedence list for Holl basis *)

    dim =0;
	zv = {};
	gen$basis = {};
	tog = {};         (* basis conversion in->g *)
    GList[g] ^= {};
	gpos = Table[0, {ngen}];
  $tm = TimeUsed[]; (* timer *)
    If [grmin>1, gen$rng[i_]:=0 /; 0<i<grmin];
	For[r=grmin, r<=maxGrade$, r++,         (* loop over grade *)
      DPrint[1, "Computing grade ", r, "  (", N[TimeUsed[ ]-$tm,4]," sec)" ]; $tm = TimeUsed[];
	  dPrev = dim;

	  (* adding the generators *)
  	  If[r<=grmax,
	    For[i=1, i<=ngen, i++,
		  zg = gvalues[[i]];
		  ri = If[glist===Auto, grade$fn[zg], glist[[i]]];
		  If[Abs[ri]==r,
		    ++dim;
		    zv = {zv, zg};
		    zg = VNormal[LinearChange[zg,tog]]; 
			gen$basis = {gen$basis, If[gnames===False, g[dim], gnames[[i]]]};
	    	If [gen$super, par = {par, P[zg]} ];
	    	gen$prev = {gen$prev, 0};	  (* Hall basis list *)
	    	sv = VSolve[ zg==g[dim], MatchList[zg,bs]][[1]]; 
	    	tog = Map[VNormal, Join[ LinearChange[tog,sv], sv ], {2}];
			DPrint[4, "sv: ", sv, ", tog: ", tog, ", bas: ", MatchList[zg,bs], ", zv:", zv];
	        gen$var[_,i] = g[dim];
			gpos[[i]] = dim;
			GList[g] ^= Flatten[{GList[g],ri}]
		]];
		zv = Flatten[zv];
		gen$basis = Flatten[gen$basis];
        gen$prev = Flatten[gen$prev];
	    If [gen$super,
		  par = Flatten[par];
		  If[pg!=pin, par = 1 - par];
		  gen$par = Join[gen$par, par];
		  par = {}];
	   (* extend the table if required *)
	    If[dim>Length[gen$tbl],  (* extend the table if required *)
	        gen$tbl = Join[gen$tbl, Table[None, {ii, Length[gen$tbl]+1, dim}, {ii}]];
	        If[sqr, gen$sqr = Join[gen$sqr, Table[None, {ii, Length[gen$sqr]+1, dim}]]]];
	DPrint[2, "Included ", dim-dPrev, " generator(s) of degree ", r];
   	DPrint[4, "Basis conversion tog: ", tog]
	  ];

      gen$ind[r] = {dPrev+1,dim+1};
      If [r>2*gen$rng[], Break[]];

      GList[g] ^= If[glist===Auto, grade$fn /@ zv, calcGList[GenBasis[g],glist,gpos]];
	  DPrint[4, "Grades: ", GList[g]];

    (*  adding the generated elements *)
	  gen$rng[r] = 1;
	  dm = 0;
	  Do [dm = Max[dm, gen$rng[i]+gen$rng[r-i]], {i,1,r/2}];
	  For[d=2, d<=rn, d++,   (* loop over degree in terms of generators *)
	  DPrint[2,"Calc deg=",d, " (dm=", dm, ", gen$rng[]=", gen$rng[], ", gen$rng[r]=", gen$rng[r],")"];
        If [d>dm && d>gen$rng[]+gen$rng[r], Break[]];
		npairs = StepGenerationVG[g, r, d, rn, Brk, brk, sqr];
    (* Distribute the remaining gen$var[hl,i] among the basis and the relations *)
        For [ i=1, i<=npairs, ++i,
	     If [ gen$flag[[i]], Continue[] ];		(* y[i] was removed *)
	     z = gen$lst[[i]] /. { brk->Bracket[in], g[k_]:>zv[[k]] }; (* image *)
         z = VNormal[z];
	     zg = VNormal[ LinearChange[z, tog] ];	(* in {g} basis *)
	     vars = MatchList[zg, bs];		(* remaining old basis *)
     DPrint[3, "gen$lst[[",i,"]]=",gen$lst[[i]], ", z=",z, ", zg=",zg, ", vars=",vars];
	    If [vars==={},				(* no old ==> relation *)
	       gen$rel = Append[ gen$rel, gen$lst[[i]]==zg ];
	       gen$var[_,i] = zg,			(* in {g} basis *)
	    (*else*)				(* add to {g} basis *)
	       gen$basis = {gen$basis, gen$lst[[i]]};  (* generation list *)
	       AppendTo[ zv, z ];			     (* image list *)
	       If [gen$super, par = {par, P[ gen$lst[[i]] ]} ];
	       gen$prev = {gen$prev, gen$lst[[i,1,1]]};	  (* Hall basis list *)
	       sv = VSolve[ zg==g[++dim], vars][[1]]; 
	       tog = Map[VNormal, Join[ LinearChange[tog,sv], sv ], {2}];
	       gen$var[_,i] = g[dim]
	    ]
      ];
      DPrint[1, "distribute -> ", N[TimeUsed[ ]-$tm,4], " sec" ]; $tm = TimeUsed[];
      gen$tbl = gen$tbl//.RestoreSV;		(* replace all gen$var[i] *)
      If[sqr, gen$sqr = gen$sqr//.RestoreSV];
      AppendTo[gen$ind[r], dim+1];
      rdim = gen$ind[r][[-1]] - gen$ind[r][[-2]];
      If [rdim>0,
    	gen$rng[r] = d;
		If[r>gen$rng[], gen$rng[] = r];
	    (* gen$deg = Join[gen$deg, Table[r, {rdim}]]; *)
        gen$prev = Flatten[gen$prev];
      ];
      If [gen$super,
        par = Flatten[par];
	    If[pg!=pin, par = 1 - par];
	    gen$par = Join[gen$par, par];
	    par = {};
        l = Plus @@ gen$par;
        DPrint[1, "r = ", r,  ", deg = ", d,  ": Dim = (", dim-l, "|", l, ")" ],
      (*else*)
	    DPrint[1, "r = ", r,  ", deg = ", d,  ": Dim = ", dim]
      ];
      gen$basis = Flatten[gen$basis];
      GenBasis[g] ^=  gen$basis //. g[i_] :> gen$basis[[i]];
      GenRel[g] ^= gen$rel //. g[i_] :> gen$basis[[i]];
      DPrint[2, GenRel[g] ];
   ]];
   ActTable[g] ^= VNormal[gen$tbl];			(* Final assignment *)
   If[sqr,
     SqrTable[g] ^= VNormal[gen$sqr];
     TableBracket[g, Brk, Unevaluated[ActTable[g]], brk, rn, Unevaluated[SqrTable[g]]],
   (* else *)
     TableBracket[g, Brk, Unevaluated[ActTable[g]], brk, rn]
   ];
   ToDegree[g] ^= rn;
   ToGrade[g] ^= maxGrade$;
   RangeIndex[g] ^= gen$ind;
   gen$basis = Flatten[gen$basis];
   GenBasis[g] ^=  gen$basis //. g[i_] :> gen$basis[[i]];
   GenRel[g] ^= gen$rel //. g[i_] :> gen$basis[[i]];
   With[{brk=Bracket[in], bs = BasisPattern[in]},
	g/: Brk[g[i_], y:bs] := brk[Image[g][[i]], y]];
(*    JacRel[g] ^= jrel; *)
   props = ComplementKeys[{opts}, {Clear, Grade, Weight}];
   SubSpace[g, in, zv, Clear->False, Hold[PiOrder]->(pg!=pin), Sequence@@props];
   DPrint[1, StringForm["Dim[``] = ", g], FDim[g] ];
   Clear["$`gen$*"];
   Bracket[g] ^= Brk;
   BracketMode[g] ^= Tabular;
   TheAlgebra[g] ^= g;
   TheModule[g[_]] ^= g; 
   GList[g] ^= If[glist===Auto, grade$fn /@ Image[g], calcGList[GenBasis[g],glist]];
   maxGrade$=.;
   WList[g] ^= wt /@ Image[g];
   g::usage = SPrint["`` is a sublagebra in ``", g, in]
]


calcGList[ex_List, glist_List, gpos] := 
  Module[{x, n = Length[glist]},
  (Deg /@ (ex /. Table[ex[[gpos[[i]]]] -> x[i], {i, n}])) /. 
      Table[Deg[x[i]] -> glist[[i]], {i, n}]]


(* --------- AlgebraDecomposition ------------------------------------ #)
>
>	Decomposition of an algebra in subalgebras
>
>   Arguments:
>	f   - the name of the decomposition
>	g   - the name of the algebra
>       {s1, ..} - the list of subalgebras. Every si is either a name
>		of an alredy defined subalgebra, or name->{g1, ..},
		where {g1,...} is a list of generators.
>   Options :
>	ToDegree->rn  - evaluate subalgebras up to degree rn
>	SubAlgebra->s - gives the name to s1+s2+...
>	GList->{gl1,...} is the list of grades for generators of components. Every gl may be
>         (1) a list of grades of generators; (2) a number, common grade for all generators
>         of this components; (3) Auto to inherit the grade
>   Results:
>	In addition to generation of subalgebras, the operation between
>	the components is defined
>
(# --------------------------------------------------------------- *)

AlgebraDecomposition::par = "No parity of `` defined. Assumed 0."

AlgebraDecomposition[f_, g_, components_, opts___] :=
  Module[{Brk, gbrk, ncomp, names, img, x, y, imx, imy, eq, sol, sub, par, glist, opt},
   gbrk = Bracket[g];
   opt = {opts};
   Brk = Bracket /. opt /. Bracket->Act;
   glist = GList /. opt;
   opt = ComplementKeys[opt, {GList}];
   par = P[Brk];
   If[!NumberQ[par], 
      Message[AlgebraDecomposition::par, Brk];
      par = 0];
   sub = SubAlgebra /. opt /. SubAlgebra->g;
   names =
     MapIndexed[
      If[AtomQ[#1],
        #1,
	SubAlgebra[#[[1]], g, #[[2]], Sequence@@opt,
          If[glist===GList || glist[[ #2[[1]] ]]===Auto, Unevaluated[], GList->glist[[ #2[[1]] ]]]];
          #1[[1]]
      ]&, components];
   DPrint[2, "DecompositionList = ", names];
   ncomp = Length[components];
   img = Image /@ names; 
   eq = Flatten[
     Table[names[[j]][i]==img[[j,i]], {j,1,ncomp}, {i,1,Dim[names[[j]]]}]];
   sol = VSolve[eq, MatchList[eq,BasisPattern[g]]][[1]];
   DPrint[2, "DecompositionRule = ", sol];
   (*sol = VSolve[eq, Basis[g]][[1]];*)
   Do[ imy = img[[iy]];
       y = names[[iy]];
     Do[ imx = img[[ix]];
      	 x = names[[ix]];

       DPrint[3, "Calculating bracket [", x, ", ", y, "] ... (",Length[imx],"*",Length[imy]," pairs)"];
		 ActTable[x,y] ^= Table[VNormal[LinearChange[VNormal[gbrk[imx[[i]],imy[[j]]]],sol]],
	       		{i,1,Length[imx]}, {j,1,Length[imy]}];
       With[{x=x,y=y},
	     Brk[x[i_], y[j_]] ^:= ActTable[x,y][[i,j]];
	     If[EvenQ[par],
	       Brk[y[j_], x[i_]] ^:=
	         SVTimes[-(-1)^(P[y[j]]P[x[i]]), ActTable[x,y][[i,j]]],
 	       Brk[y[j_], x[i_]] ^:=
	         SVTimes[-(-1)^((P[y[j]]+1)(P[x[i]]+1)), ActTable[x,y][[i,j]]]]
	       ],
       {ix,1,iy-1}],
     {iy,2,ncomp}];
   If[sub=!=g,
       	Define[sub, {Vector, Output->Subscripted, (*TeX->Subscripted,*)
		Standard->Subscripted, Traditional->Subscripted}];
	BasisPattern[sub] ^= Alternatives @@ Blank/@ names;
 	DecompositionRule[sub, f] ^= {};
        Bracket[sub] ^= Brk;
        Dim[sub] ^= Plus @@ Dim /@ names;
        PDim[sub] ^= Plus @@ PDim /@ names;
        Relatives[sub] ^= {sub, None, None, None, None, None, None, None};
	If [(Enum /.{opts}) =!= False,		(* enumeration *)
   	  With[{s=sub},
	    EnumJoin[s, Sequence @@ names]]
        ];
   ];
   DPrint[1, "Done decomposition ", f, " : ", sub, " -> ", names];
   g/: DecompositionRule[g,f] = sol;
   With[{s=sub},
     s/: DecompositionList[s,f] = names];
]


DefSubAlgebra[n_, in_, el_, opts___Rule] :=
  Module[ {i, j, dim, dima, eq, ee, seq, tbl, tbr, ptrn, brk, img=el, nAct, nact, split, sqr, sqrtab},
    split = KeyValue[{opts},Split];
    If[split=!=False, Return[DefSubAlgebra[n,in,el,split,Sequence@@ComplementKeys[{opts},{Split}]]]];
    DPrint[1, "Defining subalgebra ",n," \[Subset] ",in];
    Vector[n];
    ptrn = BasisPattern[in];
	brk = Bracket[in];
    nAct = Bracket /. {opts} /. Bracket->Act;
    nact = bracket /. {opts} /. bracket->act;
    sqr = Squaring/.{opts}/.Squaring:>($p===2);
    sqrtab = If [sqr, Table[0, {dim}], Null];
    tbl = {};
    dim = Length[el];
    eq = Table[ n[i]==el[[i]], {i, dim} ];
    seq = Dispatch[ VSolve[ eq, MatchList[eq, ptrn] ][[1]] ];
    For[ j=1, j<=dim, ++j, 
      tbr = vl @@ Table[0, {j}];
      For[ i=1, i<=j, ++i,
        l = brk[ img[[i]], img[[j]] ];
        If [l==0,  Continue[] ];   
        r =  VNormal[l /. seq ];
        If[r=!=0, DPrint[3, act[n[i], n[j]], " = ", r]];
        If[ FreeQ[ r, ptrn ],  tbr[[i]] = r;  Continue[] ];
        ++dim;
        l = VNormal[ l ];
        AppendTo[img, l];
        tbr[[i]] = n[dim];
        AppendTo[ eq, n[dim]==l ];
        DPrint[2, "Generated ",n[dim], " = [", n[i], ",", n[j], "] = ", l];
        seq = Dispatch[ VSolve[ eq, MatchList[eq, ptrn] ][[1]] ]
      ];
      tbl = { tbl, tbr };
      DPrint[If[j===1 || Mod[j,10]===0, 1, 2], "Done ", j, " of ", dim];
      If [sqr,
        l = Squaring[nAct][img[[j]]];
        If [l==0,  Continue[] ];
        r =  VNormal[l /. seq ];
        If[r=!=0, DPrint[3, n[j], "^[2] = ", r]];
        If[ FreeQ[ r, ptrn ],  sqrtab[[j]] = r;  Continue[] ];
        Message[DefSubAlgebra::noinvsq, n, ai, r];
        Return[$Failed]];
    ];
    Bracket[n]^=nAct;
    bracket[n]^=nact;
    TableBracket[n, nAct, Unevaluated[ActTable[n]], nact, Infinity, sqrtab];
(*
    Act[n[i_], n[j_]] ^:=
      If[i<=j, ActTable[n][[j,i]],
         SVTimes[(-1)^(P[n[i]]P[n[j]]),	ActTable[n][[i,j]]]];
*)
    BracketMode[n] ^= Tabular;
    ActTable[n] ^= Flatten[tbl]  /. vl->List;
    SubSpace[n, in, img, Sequence@@ComplementKeys[{opts}, {Split}]];
    Grade[n[i_]] ^:= GList[n][[i]];
    GList[n] ^= Grade /@ Image[n];
    Weight[n[i_]] ^:= WList[n][[i]];
    WList[n] ^= (Weight /. {opts}) /@ Image[n];
    TheAlgebra[n] ^= n;
    TheModule[n[_]] ^= n; 
  ]

DefSubAlgebra::noinv = "The subspace `` is not a subalgebra: [``, ``] = `` is out of the subspace"
DefSubAlgebra::noinvsq = "The subspace `` is not a subalgebra: [``]^[2] = `` is out of the subspace"

DefSubAlgebra[n_, in_, el_, split_, opts___Rule] :=
  Module[ {i, j, dim, dima, eq, ee, seq, tbl, tbr, ptrn, brk, img, gi, mg=None,
            abas, gr, eqgr, seqgr, la, ia, ai, mj, lj, toimg={}, nAct, nact, sqr, sqrtab, sqi},
      DPrint[1, "Defining graded subalgebra ",n," \[Subset] ",in];
      Vector[n];
      ptrn = BasisPattern[in];
	  brk = Bracket[in];
      nAct = Bracket /. {opts} /. Bracket->Act;
      nact = bracket /. {opts} /. bracket->act;
    grade$fn = Grade /. {opts};
	Which [
	  ListQ[grade$fn],
	    maxGrade$=grade$fn[[2]]; 
	    grade$fn = grade$fn[[1]],
	  NumberQ[grade$fn],
	    maxGrade$=grade$fn; 
	    grade$fn = Grade,
	  True,
	    maxGrade$=Infinity
	];
      tbl = {};
      If [el===All,
        img = Basis[in];
        dim = Length[img],
      (*else*)
        img = el;
        dim = Length[el]];
      sqr = Squaring/.{opts}/.Squaring:>($p===2);
      sqrtab = If [sqr, Table[0, {dim}], Null];
      eq = SplitList[Table[ n[i]==img[[i]], {i, dim} ], _, split[#[[2]]]&];
      DPrint[3, "Equations: ", eq];
      seq = ApplySplit[ Dispatch[ VSolve[ #, MatchList[#, ptrn] ][[1]] ]&, eq];
	  lj = dim;
      DPrint[4, "Solutions: ", seq];
      For[ j=1, j<=dim, ++j,
	    If[j>lj,
		  sqrtab = Join[sqrtab, Array[0,dim-lj]];
		  lj = dim;
		  img = Join[img,Flatten[toimg]];
		  toimg={}
		];
        mj = img[[j]];
        If [maxGrade$<Infinity,
          gi = grade$fn[mj];
          mg = If[NumberQ[gi], maxGrade$-gi, None]
        ];
	    tbr = vl @@ Table[0, {j}];
	    For[ i=1, i<=j, ++i,
	      ai = img[[i]];
              sqi = sqr && i==j;
          If [NumberQ[mg] && grade$fn[ai]>mg, tbr[[i]]=nact[n[i],n[j]]; Continue[]];
          l = If[sqi, Squaring[ai,brk], brk[ai, mj]];
          If [l==0,  Continue[] ];
		  gr = split[l];
          r =  VNormal[l /. PartSplit[seq,gr,{}] ];
		  If[r=!=0, DPrint[3, If[sqi, Squaring[n[i],act], act[n[i], n[j]]], " = ", r]];
          If[ FreeQ[ r, ptrn ],
            If[sqi, sqrtab[[i]] = r; tbr[[i]] = VNormal[2~SVTimes~r],
            (*else*) tbr[[i]] = r];
            Continue[] ];
          If[ el===All,
            If[sqi, Message[DefSubAlgebra::noinvsq, n, ai, r], Message[DefSubAlgebra::noinv, n, ai, mj, r]];
            Return[$Failed]];
          ++dim;
	      l = VNormal[ l ];
		  toimg = {toimg, l};
          If[sqi, sqrtbl = n[dim]; tbr[[i]] =  VNormal[2~SVTimes~n[dim]],  tbr[[i]] = n[dim]];
	      eq = JoinSplit[eq, {gr->{n[dim]==l}}];
	      DPrint[4, "New equations: ", eq];
	      eqgr = PartSplit[eq, gr,{}];
	      DPrint[2, "Generated ",n[dim], " = ", l, ", deg=", gr];
	      DPrint[4, "Solving: ", eq];
	      seqgr = Dispatch[ VSolve[ eqgr, MatchList[eqgr, ptrn] ][[1]] ];
	      seq = MergeSplit[#&, {gr->seqgr}, seq];
	      DPrint[4, "Solutions: ", seq];
	    ];
	    tbl = { tbl, tbr };
	    DPrint[If[j===1 || Mod[j,10]===0, 1, 2], "Done ", j, " of ", dim];
      ];
      SubSpace[n, in, img, opts];
      Bracket[n]^=nAct;
      bracket[n]^=nact;
      BracketMode[n] ^= Tabular;
      TableBracket[n, nAct, Unevaluated[ActTable[n]], nact, Infinity, sqrtab];
(*
      Act[n[i_], n[j_]] ^:=
        If[i<=j, ActTable[n][[j,i]],
         SVTimes[(-1)^(P[n[i]]P[n[j]]),	ActTable[n][[i,j]]]];
*)
      ActTable[n] ^= Flatten[tbl]  /. vl->List;
      Grade[n[i_]] ^:= GList[n][[i]];
      GList[n] ^= grade$fn /@ Image[n];
      Weight[n[i_]] ^:= WList[n][[i]];
      WList[n] ^= (Weight /. {opts}) /@ Image[n];
      TheAlgebra[n] ^= n;
      TheModule[n[_]] ^= n; 
  ]

SetProperties[ TestGrade,
		{Scalar, Vector->First, Homogen->0, ThreadGraded, LogPower->Times, TestAll}]

TestGrade[v_] := Grade[v]

TestGrade[v_VPlus] :=
 With[{pp = Union[Simplify /@ TestGrade /@ List @@ v]},
   If[Length[pp]==1, First[pp], Mixed]]

TestGrade[v_VSum] :=
 With[{pp = Simplify[TestGrade[First[v]]],
	 ind = First /@ Rest[List @@ v]},
   If[Select[ ind, (!FreeQ[pp,#])&, 1], Mixed, pp]]

DPrint[1, "SuperLie`Subalg` loaded"]

End[]
EndPackage[]



