(*********************** Verma Modules *********************)

BeginPackage["SuperLie`Irrmod`", {"SuperLie`", "SuperLie`Enum`", "SuperLie`Space`",
 "SuperLie`Generate`", "SuperLie`Domain`", "SuperLie`Solvars`", "SuperLie`Vsplit`"}]

SuperLie`Irrmod`HWModule::usage = "HWModule[name, alg, wt] build the irreducible
module with highest weight wt";

Begin["$`"]

(* --------- HWModule ------------------------------------------ #)
>
>	Builds a minimal module with the given highest weight.
>
>   Arguments:
>   v   - the name of the new module
>   g   - the algebra acting of the module
>   wt  - the given highest weight. Should be a list of appropriate size
>         The symbolic weights are generally not supported.
>
>   Options:
>	P->p        - the parity of the highest vector (default 0)
>	ToGrade->rn   - compute down to the grade -Abs[rn] (default - Infinity).
>        The grade of the highest vector is assigned to 0.
>        With ToGrade->Auto the range limit is adjusted as needed. 
>	Order->{y1,...,ym}  - the order in which the elements of g_ should
>        appear in the expressions of the basis of v in terms of
>        generators of U(g_). Default order is given by Basis[g_].
>	Quotient -> False  - Do not pass to quotient modulo maximal submodule
>	 (i.e., build Verma module)
>   See also VectorSpace for general options.
>
>   Prerequisites:
>   1. The Cartan decomposition of the algebra g should be defined by call of
>      Subalgebra[x, g, generators]  (positive part)
>      Subalgebra[h, g, generators]  (zero part)
>      Subalgebra[y, g, generators]  (negative part)
>      AlgebraDecomposition[CartanTriade, g, {x, h, y}]
>   2. The function Grade should be defined on g and should agree with Cartan
>      decomposition (the sign of the grade should discriminate the parts)
>   3. The function Weight should be defined on g and should agree with Cartan
>      subalgebra h: [h[i],g]=Weight[g][[i]]g
>
(# --------------------------------------------------------------- *)

HWModule[v_, g_, wt_, opts___Rule] :=
  Module[{i,j,k,l,m,q,r,s, j1={2}, adf={}, adx={{}}, y, y0, eq,	rn, rn0,
		srel, none, rel={}, bf, rngf, rnx, rngx, props, clr, cont,
  		ind, minind, dimf, rj, fi, flist, tind, gen={v[1]}, ii, cf, factor,
  		split=KeyValue[{opts}, Split], srels, spl, cfl, yl,
		rnf, z={v[1]}, zt, an, na, comp=DecompositionList[g,CartanTriade]},
  Vector[y, none];
  Scalar[cf];
  If[Length[comp]=!=3,
    Message[HWModule::comp, g];
    Return[$Failed]];
  rn = ToGrade /. {opts};
  If[rn===ToGrade, rn = Grade /. {opts} /. Grade->Infinity];
  With[{x=comp[[1]], h=comp[[2]], f=comp[[3]]},
    bf = Basis[f];
    rnf = - Min @@ Grade /@ Basis[f]; (* maximal -grade in y *)
    dimf = Dim[f];
    clr = (Clear /. {opts});
    If[clr===Continue,  (* continue with new range limit *)
       {factor,flist,gen,ind} = info[v];
       rn0 = ToGrade[v];
       adx = ActTable[x,v];
       adf = ActTable[f,v];
       j1 = RangeIndex[v];
       z = GenBasis[v];
       rel = GenRel[v];
       DPrint[1, "Continue HWModule to grade ", rn];
       cont = True,
    (*else*)
       rn0 = 0;
       ind = {dimf+1};
       If [clr=!= False, Clear[v]];
       factor = ((Quotient /. {opts})=!=False) && ((Factor /. {opts})=!=False);
       flist = Order /. {opts};
       cont = (rn===Auto);
       Vector[v];
       (* Action *)
       v/: Act[x_g, y_v] := Act[x/.DecompositionRule[g,CartanTriade], y];
       v/: Act[h[i_], v[j_]] := Weight[v[j]][[i]] ~SVTimes~ v[j];
       v/: Act[x[i_], v[j_]] :=
	  If [ Grade[x[i]]+Grade[v[j]]<=0, ActTable[x,v][[j,i]], 0 ];
       If [cont,
          v/: Act[f[i_], v[j_]] :=
               (If [ Grade[f[i]]+Grade[v[j]]<-ToGrade[v], HWModule[v,g,wt,Clear->Continue,ToGrade->-(Grade[f[i]]+Grade[v[j]])]];
                ActTable[f,v][[j,i]]);
          Basis[v,r_/;r>0] ^:=
               (If [r>ToGrade[v], HWModule[v,g,wt,Clear->Continue,ToGrade->r]]; Array[v,Dim[v,r],RangeIndex[v][[r]]]);
          Dim[v,r_/;r>0] ^:=
               (If [r>ToGrade[v], HWModule[v,g,wt,Clear->Continue,ToGrade->r]]; RangeIndex[v][[r+1]] - RangeIndex[v][[r]]),
       (*else*)
          v/: Act[f[i_], v[j_]] :=
	     If [ Grade[f[i]]+Grade[v[j]]>=-ToGrade[v],
		(*then*) ActTable[f,v][[j,i]],
		(*else*) act[f[i],v[j]]];
          Basis[v,r_/;r>0&&r<=ToGrade[v]] ^:=
             Array[v, Dim[v,r], RangeIndex[v][[r]]];
          Dim[v,r_/;r>0&&r<=ToGrade[v]] ^:=
             RangeIndex[v][[r+1]] - RangeIndex[v][[r]];

	  ];
	  
     (* Dimensions of range components *)
        v/: Dim[v,0] = 1;
        Dim[v] ^= 1;
        Dim[v,d_/;d<0] ^:= Dim[v,-d];
        v/: Basis[v,0] = {v[1]};
        Basis[v,d_/;d<0] ^:= Basis[v,-d];

     (* Define parity function *)
        PList[v] ^= {P/.{opts}/.P->0};
        P[v[i_]] ^:= PList[v][[i]];

     (* Weight and grading *)
        Weight[v[1]] ^= If[SymbolQ[wt], Array[wt,NGen[f]],wt];
        Weight[v[j_]] ^:= Weight[GenBasis[v][[j]]];
        Grade[v[i_]] ^:= GList[v][[i]];
        GList[v] ^= {0};
        PolyGrade[v[1]] ^=  Table[0, {NGen[f]}];
        PolyGrade[v[i_]] ^:= PolyGrade[GenBasis[v][[i]]];

        VectorSpace[v, Clear->False, Enum->False,
           Sequence@@ComplementKeys[{opts}, {Grade, P, Order, Dim, PList, Quotient, Factor, Clear, Split}]];
        Basis[v]^:=Array[v,Dim[v]];
        PDim[v]^=With[{s=Plus@@PList[v]},{Dim[v]-s,s}];
        NGen[v] ^= NGen[f];
        Bracket[v]^=Act;
        bracket[v]^=act;
	v::usage = SPrint["`` is a ``-module with highest weight ``", v, g, wt]
    ];
DPrint[1, "x: ", x, ", f: ", f, ", h: ", h];
    ToGrade[v] ^= If[rn===Auto, 0, rn];
    If[AtomQ[flist], flist = bf];  (* order of f[i] in U(f) *)

DPrint[2, "Grade[f]: ", Grade /@ bf, ", Grade[x] = ", Grade /@ Basis[x]];

    {rnf, rngf} = rngHW[- Grade /@ bf];
    {rnx, rngx} = rngHW[Grade /@ Basis[x]];

DPrint[1, "rngx = ", rngx, ", rngf = ", rngf];

    For [r=rn0+1; k=Dim[v,rn0], r<=rn, ++r,  (* loop over grade *)
      If[r>rnf-Grade[v[Dim[v]]], Break[]];   (* no new elements possible *)
DPrint[1, "Grade = ", -r];
      m = Min[rn-r+1, rnf];
(* Extend the multiplication table (limit width according to range) *)
      adf = Join[adf, Table[none, {k}, {If[cont, dimf, rngf[[m]]]}]];
(* Collect all ordered pairs {f[i],v[j]} with grade -r *)
      For [ii=1; l=0; zt={}; tind={},  ii<=dimf, ii++,
        fi = flist[[ii]];
        i = fi[[1]];
        minind = ii + P[fi];
        rj = r+Grade[fi];
        If[rj<0||rj>=r, Continue[]];
DPrint[3, "Searching [",fi,",v], Grade[v]=", -rj, ", j in [",If[rj==0,1,j1[[rj]]], ",", j1[[rj+1]]-1, "]"];
        For[j=If[rj==0,1,j1[[rj]]], j<j1[[rj+1]], j++,   (* loop over v[i] with grade -r-Grade[fi] *)
          If[ind[[j]]>=minind,
	    zt = { zt, act[fi,v[j]] };	(* list of expressions of grade -r *)
	    tind = {tind, ii};		(* list ordering indices *)
	    adf[[j,i]] = y[++l],	(* fill table of Lie operation *)
	  (* else *)
	    adf[[j,i]] = act[fi,v[j]]
      ] ] ];
      If [l==0,
        ToGrade[v] ^= r;
        AppendTo[j1, j1[[r]]];
        Continue[]];
      zt = Flatten[zt];
      tind = Flatten[tind];
DPrint[1, "Commutators of degree ", -r, " : ", l];
DPrint[2, "Commutators of degree ", -r, ": zt = ", zt];
(* search for dependences in {[f[i],v[j]]} *)
      If[factor,
       If[split=!=False,
        srel = {};
        ForSplit[{SplitSum[VSum[cf[i]~SVTimes~y[i], {i,l}], _, split[#/.y[j_]:>zt[[j]]]&], spl->y0},
DPrint[3, "y0 : ", spl->y0];
         eq = Table[Act[x[i], y0/.y[j_]:>zt[[j]]]==0, {i, NGen[x]}];
DPrint[3, "eq : ", eq];
         cfl = First /@ If[Head[y0]===VPlus,List@@y0,List[y0]];
         yl = Last /@ If[Head[y0]===VPlus,List@@y0,List[y0]];
         srels = SVSolve[eq, cfl ] [[1]];
DPrint[3, "srel = ", srels];
         eq = ((y0/.srels)==0);
         eq = Table[eq /. cfl[[i]]->1 /. _cf->0, {i,Length[cfl]}] /.
				{SVTimes->Times, VPlus->Plus};
DPrint[3, "Relations : ", eq];
DPrint[3, "(decoded) : ", eq/.y[i_]:>zt[[i]]];
         srels = If [$Solve===ParamSolve,
                        Block[{UserRate=hwOrderRate},ParamSolve[eq, yl]][[1]],
                (*else*)
                        orderSol[$Solve[eq, yl][[1]], y]
                ] //. $`RestoreSV;
DPrint[2, "Relations in max submodule: srel = ", srels];
DPrint[4, "(decoded) :", srels/.y[i_]:>zt[[i]]];
         srel = Join[srel, srels]
        ],
        (*else: non-split*)
         y0 = VSum[cf[i]~SVTimes~y[i], {i,l}];
DPrint[3, "y0 : ", y0];
         eq = Table[Act[x[i], y0/.y[j_]:>zt[[j]]]==0, {i, NGen[x]}];
DPrint[3, "eq : ", eq];
         srel = SVSolve[eq, Array[cf,l] ] [[1]];
DPrint[3, "srel = ", srel];
         eq = ((y0/.srel)==0);
         eq = Table[eq /. cf[i]->1 /. _cf->0, {i,l}] /.
				{SVTimes->Times, VPlus->Plus};
DPrint[3, "Relations : ", eq];
DPrint[4, "(decoded) : ", eq/.y[i_]:>zt[[i]]];
         srel = If [$Solve===ParamSolve,
                        Block[{UserRate=hwOrderRate},ParamSolve[eq, Array[y,l]]][[1]],
                (*else*)
                        orderSol[$Solve[eq, Array[y,l]][[1]], y]
                ] //. $`RestoreSV;
DPrint[2, "Relations in max submodule: srel = ", srel];
DPrint[4, "(decoded) :", srel/.y[i_]:>zt[[i]]]
      ],
      (* else: Build module Verma *)
         srel = {}
      ];
      q = Length[srel];
      k = l - q;		(* the number of new elements in y *)
DPrint[1, "New elements : ", k, ", relations: ", q];
      an = Range[l];		(* an - list of free y[i] *)
      If [q>0, (*then*)
         For [i=1, i<=q, ++i, an[[ srel[[i,1,1]] ]] = 0 ];
         an = DeleteCases[an, 0];
      ];
      na = Table[y[ an[[i]] ] -> v[i+j1[[r]]-1], {i,k} ];
      rel = Join[rel, srel/. y[i_]:>zt[[i]] /. v[i_]:>z[[i]] ];
      zt = Part[zt, an];
      ind = Join[ind, Part[tind, an]];
      gen = Join[gen, zt];
      z = Join[ z, zt /. v[i_]:>z[[i]] ];
DPrint[3, "adf = ", adf, ", na=", na, ", ind=", ind];
      adf = VNormal[adf /. srel /. na];
      v/: ActTable[f,v] = adf;
DPrint[2, "Mult. table [f,m]: adf = ", adf];
DPrint[2, "gen = ", gen];
      AppendTo[j1, j1[[r]] + k];
      ToGrade[v] ^= r;
      RangeIndex[v] ^= j1;
      GList[v] ^= Flatten[{0, Table[-i, {i, r}, {j, j1[[i]], j1[[i+1]]-1}]} ];
      adf = adf //. act[f[i_],v[j_]]:>evalHWAct[f[i],gen[[j]]];
      v/: ActTable[f,v] = adf;
DPrint[2, "Mult. table after factorization: adf = ", adf];
      q = Min[r, rnx];
      GenBasis[v] ^= z;
      adx = Join[adx, Table[ VNormal[ Act[ x[i], zt[[j]] ] ],
		{j, k}, {i, rngx[[q]]} ] ];
      v/: ActTable[x,v] = adx;
DPrint[2, "GList : ", GList[v]];
      PList[v] ^= P /@ z;
      i = j1[[r+1]]-1;
      If[ValueQ[PList[x]],
         (*then*) j = Plus @@ PList[v];
      		  DPrint[1, "r = ", r,  ", Dim = (", i-j, "|", j, ")" ],
	 (*else*) DPrint[1, "r = ", r,  ", Dim = ", i]
      ];
      GenRel[v] ^= rel;
      Dim[v] ^= j1[[r+1]]-1;
    ];
    Clear[none];
    GenBasis[v] ^= z;
    If[cont,
       info[v] = {factor,flist,gen,ind}];
    RangeIndex[v] ^= j1;
    v/: ActTable[f,v] = adf;
    v/: ActTable[x,v] = adx;
    GenRel[v] ^= rel;
    PDim[v]^=With[{s=Plus@@PList[v]},{Dim[v]-s,s}];
    TheAlgebra[v] ^= g;
    Relatives[v] ^= {v, None, None, None, None, None, None, None};
    If [(Enum /.{opts}) =!= False,		(* enumeration *)
      With[{r=Length[RangeIndex[v]]-1},
		EnumSet[v, {0,-r,-1}->
          {0 :> (v /@ Range[RangeIndex[v][[1]]-1]),
           d_:> (v /@ Range[ RangeIndex[v][[-d]], RangeIndex[v][[-d+1]]-1])}]]
    ];
   ];
   v::usage
 ];

evalHWAct[fj_,act[fi_,z_]]:=
  VNormal[
    DPrint[2,evalHWAct->{fj,fi,z, VNormal[Act[fj, z]], Act[Act[fj,fi],z], VNormal[Act[fi, Act[fj, z]]]}];
    If[fj===fi,
      If [$p===2, Act[Squaring[fi,Act],z], (*else*) SVTimes[1/2 , Act[Act[fj,fi],z]]],
    (* else *)
      Act[Act[fj,fi],z] ~VPlus~
	SVTimes[(-1)^(P[fj]P[fi]), Act[fi, Act[fj, z]]]]];

(* returns {max[rnglist], {last position of # in rnglist}} *)
rngHW[rnglist_]:=
  Module[{maxrng, indlist, i, r, dim},
    maxrng = Max@@rnglist;
    indlist = Table[0,{maxrng}];
    dim = Length[rnglist];
    For[i=1,i<=dim,i++,
      r = rnglist[[i]];
      If[indlist[[r]]<i, indlist[[r]]=i]];
    For[i=2, i<=maxrng, i++,
      indlist[[i]]=Max[indlist[[i]], indlist[[i-1]]]];
    {maxrng, indlist}];

(* transform solution to ensure that y_i are expressed via y_j with j>i *)
orderSol[orig_, y_] :=
  Module[{si, sol=orig, dim=Length[orig], i, isol, imin},
    For[i=1, i<=dim, i++,
      si = sol[[i]];
      isol = si[[1,1]];
      imin = MatchMin[si[[2]], y, isol];
      If[imin<isol,
        si = $Solve[si[[1]]==si[[2]], y[imin]][[1,1]];
        sol = Table[If[i==j, si, sol[[j,1]]->$SNormal[sol[[j,2]]/.si]], {j,dim}]]];
    sol];

MatchMin[expr_,head_,below_:Infinity] :=
  Module[{min=below},
    $`MatchPatrn=head[_];
    $`MatchFunc = ((min = Min[min, #[[1]]])&);
    $`MatchScan[expr];
    min];


HWModule::comp = VermaModule::comp =
 "Use AlgebraDecomposition[CartanTriade, ``, {x,h,y}] to define the
 Cartan subalgebra (h), positive (x) and negative (y) components."


hwOrderRate[expr_Times, ptrn_] := 
  With[{var = Cases[expr, ptrn]}, 
   If[Length[var] === 1, Position[ptrn, var[[1]]][[1, 1]], Infinity]];

hwOrderRate[expr_, ptrn_] := 
 With[{pos = Position[ptrn, expr]}, 
  If[pos =!= {}, pos[[1, 1]], Infinity]]

DPrint[1, "SuperLie`Irrmod` loaded"]

End[];
EndPackage[];


