BeginPackage["SuperLie`Free`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`",
  "SuperLie`Space`", "SuperLie`Generate`"}] 

SuperLie`Free`FreeLieAlgebra::usage =
"FreeLieAlgebra[alg, {gen}, {rel}, range] defines the (super)algebra generated
(as free algebra) by elements gen[[1]], ... with relations rel[[1]]... .
Options Grade->{gr1,...} and PList->{p1,...} defines the degrees and parities
of generators. All computation are made for elements with degree<=range."

Begin["$`"]

(* --------- FreeLieAlgebra ------------------------------------ #)
>
>	Generates a free Lie (super)algebra with relations
>
>   Arguments:
>	g   - the name of the new algebra
>	gen - the list of generators
>	rel - the list of relations between generators
>   Options :
>       ToDegree -> d  evaluate up to degree d in terms of generators
>	Grade -> {g1, ..} or GList grading of generators (default all 1)
>       ToGrade -> g evaluate up to grade g
>	PList -> list of parities of generators (default all 0)
>	Squaring->True: use Squaring[x,Act] instead of Act[x,x]
>   Results:
>	Act[g[i],g[j]] - the bracket in new algebra
>	GenBasis[g] - the basis of "g" in term of generators
>	NGen[g] - the number of generators
>	GenRel[g] - equal to rel
>	Dim[g] - the dimension of "g" (or of evaluated part of "g")
>	PDim[g] - the (even|odd) dimension of "g"
>	BasisPattern[g] - the pattern for basis elements of "g" (equal to _n)
>	ToDegree[g] - equal to the value of option ToDegree
>	Grade[g[i]] - the degree of GenBasis[g][[i]]. If all relations are
>		homogeneous, this is the grading of "g".
>
(# --------------------------------------------------------------- *)

(* static variables :
	gen$tbl, gen$ind, gen$lst, gen$rel, gen$flag
	gen$par, gen$var, gen$prev, gen$super
*)

FreeLieAlgebra::ngen = "Ambiguous number of generators";

FreeLieAlgebra[g_, gen_, rel_, opts___Rule] :=
  FreeLieAlgebra[g, gen, rel, ToDegree/.{opts}/ToDegree->Infinity, opts];

FreeLieAlgebra[g_, gen_, rel_, rn_, opts___] :=
  Module[{rng, ngen, dgen, pgen, rels, rrels, vars, sol, nrg, pos, stdGrade,
	  r, i, j, basis={}, rgen, dim=0, gentbl, gensqr, par={}, sqr },
	Clear["$`gen$*"];
    Define[g, {Vector, Output->Subscripted, BracketMode->Tabular}];
(*    Vector[gen$var]; *)
    gentbl := gen$tbl;
    sqr = Squaring/.{opts}/.Squaring:>($p===2);
    If [sqr,
      gensqr := gen$sqr;
      TableBracket[g, Act, Unevaluated[gentbl], act, Infinity, Unevaluated[gensqr]],
    (* else *)
      TableBracket[g, Act, Unevaluated[gentbl], act, Infinity]
    ];
    Grade[g[i$_]] ^:= gen$deg[[i$]];
    ToDegree[g] ^= rng = rn;
    NGen[g] ^= ngen = Length[gen];
    BasisPattern[g] ^= (_g);
    dgen = KeyValue[{opts}, GList];
    If[!dgen, dgen = KeyValue[{opts}, Grade]];		(* Degree of generators *)
    Which [dgen===False, dgen = Table[1, {ngen}],
	   Length[dgen]=!=ngen, Message[FreeLieAlgebra::ngen]; Return[$Failed]
    ];
    stdGrade = FreeQ[dgen, _?(#!=1&), 1];
    maxGrade$ = ToGrade /. {opts} /.ToGrade->Infinity;
    pgen = KeyValue[{opts}, PList];		(* Parity of generators *)
    Which [pgen===False,	P[_g] ^= 0;
				gen$super = False,
	   Length[pgen]=!=ngen, Message[FreeLieAlgebra::ngen];
				Return[$Failed],
	   True,		P[g[i_]] ^:= gen$par[[i]];
				gen$par = {};
				gen$super = True
    ];

    rels = rel;
    gen$tbl = gen$deg = gen$prev = gen$sqr = {};
    gen$ind = {1};
    $tm = TimeUsed[]; (* timer *)

   For [r=1, r<=rng, ++r,
      DPrint[1, "Step ", r];
      npairs = StepGeneration[g, r, rng, Act, act];	(* get [g[i],g[j]]'s *)
      If [rels=!={},
	rels = rels /. act[g[i_],g[j_]] :> Act[g[i],g[j]] /;
		gen$deg[[i]]+gen$deg[[j]]==r;
	rrels = Select[rels, FreeQ[#, act]&];	(* relations of degree r *)
	If [rrels=!={},				(* solve relations *)
	  vars = MatchList[rrels, _gen$var];
	  sol = VSolve[rrels, vars][[1]];
	  (gen$flag[[#[[1,-1]]]]=True; Set @@ #)& /@ sol;
        ];
	rels = Complement[rels, rrels]		(* the remaining relations *)
      ];
      DPrint[2, "Done A"];
      If [ngen>0,
	pos = First /@ Position[dgen, r];	(* generators of degree r *)
 	nrg = Length[pos];
	If [nrg>0,
	  rgen = gen[[pos]];
      DPrint[3, "pos=",pos, ", rgen=",rgen, ", pgen=",pgen];
      DPrint[3, "rels=",rels, ", dim=", dim];
	  rels = rels /. MapIndexed[#1->g[dim+First[#2]]&, rgen];
      DPrint[3, "rels=",rels];
	  basis = {basis, rgen};
	  gen$prev = {gen$prev, Table[0, {nrg}]};
	  If [gen$super, par = {par, pgen[[pos]]} ];
      DPrint[3, "basis=",basis, ", gen$prev=", gen$prev, ", par=", par];
	  dim += nrg;
	  ngen -= nrg		(* the remaining generators *)
	]
      ];
      DPrint[2, "Done B"];

      For [ i=1, i<=npairs, ++i,		(* add gen$var[i] to basis *)
	If [ gen$flag[[i]], Continue[] ];	(* gen$var[i] was removed *)
	basis = {basis, gen$lst[[i]]};
	If [gen$super, par = {par, P[ gen$lst[[i]] ]} ];
	gen$prev = {gen$prev, gen$lst[[i,1,1]]};
	gen$var[_,i] = g[++dim]
      ];

      gen$tbl = gen$tbl//.RestoreSV;		(* replace all gen$var[i] *)
      If[sqr, gen$sqr = gen$sqr//.RestoreSV];   (* replace all gen$var[i] *)
      rels = rels//.RestoreSV;
(*      Clear[gen$var];
      VectorQ[gen$var]^=True; *)
      AppendTo[gen$ind, dim+1];
      nrg = gen$ind[[-1]] - gen$ind[[-2]];
      If [nrg>0,
	If [rng==Infinity && ngen==0,  rng = 2*(r-1)];
	gen$deg = Join[gen$deg, Table[r, {nrg}]]; 
        gen$prev = Flatten[gen$prev]
      ];
      If [gen$super,
	gen$par = Join[gen$par, Flatten[par]];
	par = {};
        i = gen$ind[[r+1]]-1;
        j = Plus @@ gen$par;
        DPrint[1, "r = ", r,  ", Dim = (", i-j, "|", j, ")" ],
      (*else*)
	DPrint[1, "r = ", r,  ", Dim = ", gen$ind[[r+1]]-1]
      ]
    ];
    ActTable[g] ^= VNormal[gen$tbl];
    If [sqr,
      SqrTable[g] ^= VNormal[gen$sqr];
      TableBracket[g, Act, Unevaluated[ActTable[g]], act, rn, Unevaluated[SqrTable[g]]],
    (* else *)
      TableBracket[g, Act, Unevaluated[ActTable[g]], act, rn]
    ];
    GList[g] ^= gen$deg;
    Grade[g[i_]] ^:= GList[g][[i]];
    If [gen$super, P[g[i_]] ^:= PList[g][[i]];  PList[g] ^= gen$par];
    basis = Flatten[basis];
    GenBasis[g] ^= basis //. g[i_] :> basis[[i]] ;
    GenRel[g] ^= rel;
    RangeIndex[g] ^= gen$ind;
    If [stdGrade,
       g/: Dim[g,r_/;r>0&&r<=ToDegree[g]] :=
		RangeIndex[g][[r+1]] - RangeIndex[g][[r]],
    (* else *)
       gen$rng = Max @@ GList[x];
       g/: Dim[g,r_] := Count[GList[x],r]
    ];
    Dim[g] ^= gen$ind[[rng+1]]-1;
    If [gen$super,
       If [stdGrade,
          g/: PDim[g,r_/;r>0&&r<=ToDegree[g]] :=
		Count[Take[PList[g], RangeIndex[g][[r]],
		 		RangeIndex[g][[r+1]]-1], #]& {0, 1},
       (* else *)
          g/: PDim[g,r_] := Count[Inner[If[#1==r,#2]&,Glist[g],Plist[g],List],#]& /@ {0,1}
       ];
       PDim[g] ^= Count[PList[g], #]& /@ {0,1},
    (* else*)
       g/: PDim[g,r_] := { Dim[g, r],0 };
       PDim[g] ^= { Dim[g], 0 }
    ];
    If [(Enum /.{opts}) =!= False, 		(* enumeration *)
      With[{r=gen$rng},
       If [stdGrade,
	  EnumSet[g, {1,r,1}->{d_:> (g /@
		Range[RangeIndex[g][[d]], RangeIndex[g][[d+1]]-1])}],
       (*else*)
          EnumSet[g, {0,r,1}->{d_:> Select[Array[g,Dim[g]],Grade[#]==d&]}]
    ]]];
    Clear["$`gen$*"];
    g::usage = SPrint["`` is generated as free agebra with `` generator(s) and `` relation(s)",
      g, ngen, Length[rel]]
  ]

End[]
EndPackage[]

