BeginPackage["SuperLie`Cartmatr`",
  {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`", "SuperLie`Space`", "SuperLie`Generate`"}]

SuperLie`Cartmatr`CartanMatrixAlgebra::usage =
"CartanMatrixAlgebra[name, {x,h,y}, matr] defines a Lie (super)algebra
with given Cartan matrix \"matr\". It's elements are named h[i] (Cartan 
subalgebra), x[i] (positive weight), y[i] (negative weight). The parities
and the grading of positive generators may be defined using options
PList->{p1, ...} and GList->{g1, ...}. The option ToDegree->d and ToGrade->g
limits computations up to terms of polynomial degree d and grading g.";


SuperLie`Cartmatr`CartanMatrix::usage = 
"If the algebra g is constructed from Cartan matrix, CartanMatrix[g] returns that matrix."; 

SuperLie`Cartmatr`RootReflection::usage =
"For an algebra g constructed from Cartan matrix, RootReflection[g,i] returns the matrix
of reflection about the i-th simple root. These reflections generate the Weyl group of
the algebra g."

SuperLie`Cartmatr`WeightToPolyGrade::usage = 
"WeightToPolyGrade[g,w] converts the weight w from the basis given by the action of
the Cartan subalgebra to the basis of simple positive roots"

SuperLie`Cartmatr`PolyGradeToWeight::usage =
"PolyGradeToWeight[g,d] converts the weight d from the basis of simple positive roots
to the basis given by the action of the Cartan subalgebra"


Begin["$`"]

(* --------- CartanMatrixAlgebra ------------------------------------ #)
>
>	Generating an algebra from its Cartan matrix
>
>   Arguments:
>	g   - the name of the new algebra
>	{x, h, y} - gives the names of generators x[i], h[i], y[i]
>	cam - the Cartan matrix
>   Options :
>	PList -> list of parities of generators (default all 0)
>	GList -> list of gradings of positive generators (default all 1)
>	ToGrade -> d: calculate up to grade d (default Infinity) [old option: Grade]
>	ToDegree -> d: evaluate up to degree d of polynomials of generators (default Infinity) [old option: GRange]
>   Squaring->True: use Squaring[x,Act] instead of Act[x,x]
>   Results:
>	Act - the bracket in new algebra
>	GenBasis[g] - the basis of positive part of "g" in term of generators
>	NGen[g] - the number of positive generators
>	GenRel[g] - relations between positive generators
>	Dim[g] - the dimension of "g" (or of evaluated part of "g")
>	PDim[g] - the (even|odd) dimension of "g"
>	BasisPattern[g] - the pattern for basis elements of "g" (equal to _x|_h|_y)
>	ToDegree[g] - equal to input option ToDegree
>	Grade[x[i]] (and also h[i], y[i]) - the grading in algebra "g".
>
(# --------------------------------------------------------------- *)

CartanMatrixAlgebra::ngen =
 "The length of PList/GList should be equal to the size of the Cartan matrix";


CartanMatrixAlgebra[g_, {x_, h_, y_}, cam_, opts___Rule] :=
  Module[{i,j, rel={}, jrel={}, d, options,
	  l, lr, z={}, pz={}, k, eq={}, adl={}, ad0, y0, cf, rr, rep, zs, cdim,
	  s, sv, srel, an, ca, na, q, r, t, z0, zt, pzt, j1={1}, sm, adQ, dim,
	  maxrng=2, inv, refl, rn, opt, opth, stdGrade, nh },
    Scalar[cf];
    Clear["$`gen$*"];

    options = {opts} /. {HoldPattern[Grade->a_]:>(ToGrade->a), HoldPattern[GRange->a_]:>(ToDegree->a)};
    sqr = Squaring/.options/.Squaring:>($p===2);
(*    opt = ComplementKeys[options,{PList,GList,Grade,ToGrade,ToDegree,Squaring}];  *)
    opt = ComplementKeys[options,{PList,GList,Squaring,Enum}];
    opth = ComplementKeys[opt,{ToGrade,ToDegree}];
    Algebra[x, Enum->False, BracketMode->Tabular, Bracket->Act, Sequence@@opt];
    Algebra[h, Enum->False, BracketMode->Tabular, Bracket->Act, Sequence@@opth];
    Algebra[y, Enum->False, BracketMode->Tabular, Bracket->Act, Sequence@@opt];
    Define[g, {Vector, Output->Subscripted, TeX->Subscripted,
		Standard->Subscripted, Traditional->Subscripted}];
(*    Vector[gen$var]; *)

(* Check if "cam" is square matrix; set "NGen[g]" to it's size *)
    cdim = Dimensions[cam];
    If [!MatrixQ[cam] (*|| First[cdim]!=Last[cdim]*),
		Message[CartanMatrixAlgebra::matsq, cam, 3]; Return[] ];
    ca = Transpose[cam];
    NGen[g] ^= NGen[x] ^= NGen[y] ^= ngen = Last[cdim];
    nh = First[cdim];

    dgen = Table[1, {ngen}];
    gen$deg = GList /. options /. GList->Table[1, {ngen}];
    GList[x] ^:= gen$deg;
    stdGrade = FreeQ[gen$deg, _?(#!=1&), 1];
    gen$par = KeyValue[options, PList];		(* Parity of generators *)
    maxGrade$ = ToGrade /. options /. ToGrade->Infinity;
    Which [
	   Length[gen$deg]=!=ngen,
				Message[CartanMatrixAlgebra::ngen];
				Return[$Failed],
	   gen$par===False,
				P[_x] ^= P[_y] ^= 0;
				gen$super = False,
	   Length[gen$par]=!=ngen,
				Message[CartanMatrixAlgebra::ngen];
				Return[$Failed],
	   True,	P[x[i$_]] ^:= gen$par[[i$]];
	   			P[y[i$_]] ^:= gen$par[[i$]];
				gen$super = True
    ];
    P[_h] ^= 0;

    Grade[x[i$_]] ^:= gen$deg[[i$]];
    ToDegree[g] ^= rng = rn = ToDegree/.options/.ToDegree->Infinity;
    BasisPattern[g] ^= (_x|_h|_y);
    DecompositionList[g,CartanTriade] ^= {x, h, y};
    DecompositionRule[g,CartanTriade] ^= {};
    CartanMatrix[g] ^= cam;
    If[ngen==nh && Det[cam]=!=0,
      inv = Transpose[Inverse[cam]];
      g/: CartanMatrix[g, -1] = inv;
      refl[a_,b_] := b - 2 (a.inv.b)/(a.inv.a) a;
      g/: RootReflection[g,i_Integer] := Transpose[Table[refl[#[[i]]&/@cam, WeightMark[ngen, j]], {j, ngen}]];
      g/: RootReflection[g,i_List] := Transpose[Table[refl[i, WeightMark[ngen, j]], {j, ngen}]];
      g/: RootReflection[g,i_,w_] := RootReflection[g,i].w;
      WeightToPolyGrade[g,w_] ^:= w.CartanMatrix[g, -1];
      PolyGradeToWeight[g,d_] ^:= CartanMatrix[g].d;
   ];
(* Define Lie operation *)
    gentbl := gen$tbl;
    GenBasis[x] ^:= gen$basis;
    If[sqr,
      gensqr := gen$sqr;
      TableBracket[x, Act, Unevaluated[gentbl], act, Infinity, gensqr],
    (*else*)
      TableBracket[x, Act, Unevaluated[gentbl], act, Infinity]
    ];
    h/: Act[h[i_], v:(x|y|h)[j_]] := Weight[v][[i]] ~SVTimes~ v;
    h/: Act[v:(x|y|h)[j_], h[i_]] := (- Weight[v][[i]]) ~SVTimes~ v;
    Act[y[i_], y[j_]] ^:= Act[x[i],x[j]] /. x->y;
    Act[x[i_], y[j_]] ^:=
      If [i<=NGen[g] && j<= NGen[g],
	(*then*) If [i==j, h[i], 0],
	(*else*) Act[GenBasis[x][[i]], GenBasis[x][[j]]/.x->y] //. 
				act[v:((_x|_y|_h|_Squaring)..)] :> Act[v]
      ];
    Act[v_y, w_x] ^:= (-(-1)^(P[v]*P[w])) ~SVTimes~ Act[w,v];
    y/: Squaring[y[i_],Act] := Squaring[x[i],Act] /. x->y;
 
(* Weight and grading *)
    Weight[h[_]] ^= Table[0,{nh}];
    Weight[x[j_]] ^:= If[j<=NGen[g], ca[[j]], Weight[GenBasis[x][[j]]] ];
    Weight[y[j_]] ^:= - Weight[x[j]];
    Grade[x[i_]] ^:= GList[x][[i]];
    Grade[y[i_]] ^:= - Grade[x[i]];
    PolyGrade[(c_:1)*x[i_]] :=
	If [i<=NGen[g],
		(*then*) Table[If[i==j,1,0], {j,NGen[g]}],
		(*else*) PolyGrade[GenBasis[x][[i]]]
	];
    PolyGrade[y[i_]] ^:= - PolyGrade[x[i]]; 
    PolyGrade[h[_]] ^= Table[0, {ngen}]; 

    gen$basis = Array[x, {ngen}];
    gen$prev = Table[0, {ngen}];
    gen$rel = gen$tbl = gen$sqr = {};
    gen$ind = {1, ngen+1};
    gen$rng = 1;
    dim = ngen;
    $tm = TimeUsed[]; (* timer *)

    For [r=2, r<=rn, ++r,	(*  r = current degree *)
      If [r>2*gen$rng, Break[]];
      npairs = StepGeneration[x, r, rng, Act, act, sqr];   (* get [x[i],x[j]]'s *)
(*	  If [ r==1, Break[] ]; *)
      an = First /@ Position[gen$flag, _Integer];
  DPrint[4, "Indices: ", an];
      k = Length[an];
      zs = VSum[Unevaluated[cf[i]~SVTimes~ gen$lst[[an[[i]] ]]], {i, k} ];
  DPrint[4, "Generated: ", zs];
      eq = Table[ VNormal[Act[y[i], zs] /. act->Act]==0, {i, ngen}];
  DPrint[3, "Equation: ", eq];
      srel = SVSolve[eq, Array[cf,k] ] [[1]];
  DPrint[3, "Solution: ", srel];
      rdim = k - Length[srel];
      If [rdim>0,
	y0 = Sum[
		With[{j=an[[i]]}, (cf[i]/.srel)*gen$var[gen$flag[[j]],j] ],
		{i,k}
	     ];
	eq = Table[(y0 /. cf[i]->1/. _cf->0) == 0, {i,k}];
	vars = MatchList[y0, _gen$var];
	srel = $Solve[eq, vars] [[1]];
	gen$rel =
	   {gen$rel, srel /. gen$var[_,i_]:>gen$lst[[i]] //. $`RestoreSV};
	(gen$flag[[ #[[1,-1]] ]]=True; Set @@ #)& /@ srel;
      ]; (* If rdim *)
      dim = StepExtendBasis[x, npairs, sqr];
      gen$basis = Flatten[gen$basis];
      GenBasis[g] ^= GenBasis[x] ^=
		gen$basis //. x[i_/;i>ngen] :> gen$basis[[i]];
   DPrint[4, "Basis: ", GenBasis[g]];
      GenRel[g] ^= Flatten[gen$rel] //. x[i_/;i>ngen] :> gen$basis[[i]];
   DPrint[4, "Relations: ", GenRel[g]];
    GenBasis[g] ^= GenBasis[x] ^=
		gen$basis //. x[i_/;i>ngen] :> gen$basis[[i]];
    GList[x] ^= (Grade/@(GenBasis[g]//.x->g))/.Grade[g[i_]]:>gen$deg[[i]];
    ];

    ActTable[x] ^= VNormal[gen$tbl];
    If [sqr,
      SqrTable[x] ^= VNormal[gen$sqr];
      TableBracket[x, Act, Unevaluated[ActTable[x]], act, rn, Unevaluated[SqrTable[x]]],
    (* else *)
      TableBracket[x, Act, Unevaluated[ActTable[x]], act, rn, Unevaluated[SqrTable[x]]]
    ];
    GenBasis[g] ^= GenBasis[x] ^=
		gen$basis //. x[i_/;i>ngen] :> gen$basis[[i]];
    GList[x] ^= (Grade/@(GenBasis[g]//.x->g))/.Grade[g[i_]]:>gen$deg[[i]];
    Grade[x[i_]] ^:= GList[x][[i]];
    Grade[y[i_]] ^:= -GList[x][[i]];
    Grade[_h] ^= 0;
    GenRel[g] ^= Flatten[gen$rel] //. x[i_/;i>ngen] :> gen$basis[[i]];
    RangeIndex[g] ^= RangeIndex[x] ^= RangeIndex[y] ^= gen$ind;
    If [stdGrade,
       g/: Dim[g,r_/;r>0&&r<=ToDegree[g]] :=
            RangeIndex[g][[r+1]] - RangeIndex[g][[r]];
       g/: Dim[g, 0] = ngen;
       x/: Dim[x, r_] := If[r>0, Dim[g,r], 0],
    (*else*)
       gen$rng = Max @@ GList[x];
       g/: Dim[g,r_/;r>0] := Count[GList[x],r];
       g/: Dim[g, 0] = ngen + 2*Count[GList[x],0];
       x/: Dim[x, r_/;r>0] := If[r>=0, Count[GList[x],0], 0];
    ];
    g/: Dim[g, r_/;r<0] := Dim[g,-r];
    Dim[x] ^= Dim[y] ^= dim;
    Dim[h] ^= nh;
    Dim[g] ^= 2*dim+nh;
    If [gen$super,
      PList[x] ^= gen$par;
      P[x[i_]] ^:= PList[x][[i]];
      P[y[i_]] ^:= PList[x][[i]];
      If [stdGrade,
         x/: PDim[x, r_] := If[r>0, PDim[g,r], 0];
         g/: PDim[g,r_/;r>0&&r<=ToDegree[g]] :=
               Count[Take[PList[x], RangeIndex[g][[r]],
                  RangeIndex[g][[r+1]]-1], #]& {0, 1};
         g/: PDim[g,0] = {nh,0},
      (*else*)
         x/: PDim[x, r_] := If[r>=0, Count[Inner[If[#1==r,#2]&,GList[x],PList[x],List],#]& /@ {0,1}, {0,0}];
         g/: PDim[g,r_/;r>0] :=
               Inner[If[#1==r, If[#2==0, {1, 0}, {0, 1}], {0, 0}] &, PList[x], GList[x], Plus];
         g/: PDim[g,0] = {nh,0} + 2 PDim[x,0]
      ];
      g/: PDim[g, r_/;r<0] := PDim[g,-r];
      PDim[x] ^= PDim[y] ^= Count[PList[x], #]& /@ {0,1},
    (* else*)
      P[_x] ^= P[_y] = 0;
      x/: PDim[x,r_] := { Dim[x,r], 0 };
      g/: PDim[g,r_] := { Dim[g,r], 0 };
      PDim[x] ^= PDim[y] ^= { dim, 0 };
    ];
    PDim[h] ^= {nh, 0};
    PDim[g] ^= PDim[x] + PDim[h] + PDim[y];
    y/: PDim[y, r_] := PDim[x,-r];
    Bracket[g] ^= Act;
    bracket[g] ^= act;
    TheAlgebra[g] ^= g;
    If [(Enum /.options) =!= False,		(* enumeration *)
      With[{d=ngen, hd=nh, r=gen$rng},
	EnumSet[h, {0,0,1}->{0:>(h /@ Range[hd])}];
	  If [stdGrade,
		EnumSet[x, {1,r,1}->{d_:> (x /@
			Range[ RangeIndex[g][[d]], RangeIndex[g][[d+1]]-1])}];
		EnumSet[y, {-1,-r,-1}->{d_:> (y /@
			Range[ RangeIndex[g][[-d]], RangeIndex[g][[-d+1]]-1])}],
	  (*else*)
	    EnumSet[x, {0,r,1}->{d_:> Select[Array[x,Dim[x]],Grade[#]==d&]}];
		EnumSet[y, {0,-r,-1}->{d_:> Select[Array[y,Dim[y]],Grade[#]==d&]}]
	  ];
	EnumJoin[g, h,x,y]
      ]
    ];
    (* Positions of elements in Basis[g] *)
    Act[h[i_],v_/;useBasis[g,Tag[v,Identity]]] ^:= Act[g[i],v];
    With[{d=Dim[h]}, Act[x[i_],v_/;useBasis[g,Tag[v,Identity]]] ^:= Act[g[i+d],v]];
    With[{d=Dim[h]+Dim[x]}, Act[y[i_],v_/;useBasis[g,Tag[v,Identity]]] ^:= Act[g[i+d],v]];
    useBasis[g]^=True;
    g/: ReGrade[g,gr_List] := 
       (GList[x] ^= (Grade/@(GenBasis[g]//.x->g))/.Grade[g[i_]]:>gr[[i]]);
    Clear["$`gen$*"];
    FDim[g]
  ]

CartanMatrixAlgebra[g_, {x_, h_, y_}, cam_, rng_, opts___Rule] :=
  CartanMatrixAlgebra[g, {x, h, y}, cam, ToDegree->rng, opts]


DPrint[1, "SuperLie`Cartmatr` loaded"]

End[]
EndPackage[]

