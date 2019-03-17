(**********  Poisson Algebra and Contact Algebra *************)

BeginPackage["SuperLie`Poisson`",
  {"SuperLie`", "SuperLie`Space`", "SuperLie`Vsplit`","SuperLie`Domain`",
   "SuperLie`Enum`", "SuperLie`Symalg`"}]

SuperLie`Poisson`PoissonAlgebra::usage = 
  "PoissonAlgebra[name, x] defines a Lie (super)algebra \"name\" as the algebra of
the polynomials on the space \"x\" with standard Poisson bracket. 
PoissonAlgebra[name, {p1,...,pn,[\[Theta],]qn,...,q1}] defines a Lie
(super)algebra \"name\" as the algebra of the polynomials on the direct sum of the
spaces p1,...,q1 with standard Poisson bracket on {pi,qi} and diagonal on \[Theta].
PoissonAlgebra[name, x, {{c1,i1,j1},...}] define the Poisson algebra with form
{f,g}=c1 df/dxi1 dg/dxi2 + ..."

SuperLie`Poisson`Pb::usage = "Pb[x,y] is the Poisson bracket (operator)."
SuperLie`Poisson`pb::usage = "pb[x,y] is the Poisson bracket (unevaluated form)."

SuperLie`Poisson`HamiltonAlgebra::usage = 
  "HamiltonAlgebra[name, x] defines a Lie (super)algebra \"name\" as the
algebra of the polynomials of x[1],... ,x[n] modulo constants with standard Poisson 
bracket. This algebra is isomorphic to the algebra of Hamiltonian vector fields.
HamiltonAlgebra[name, {p1,...}] defines non-standard Poisson	brackets."

SuperLie`Poisson`Hb::usage = "Hb[x,y] is the Poisson bracket modulo constants (operator).";
SuperLie`Poisson`hb::usage = "hb[x,y] is the Poisson bracket modulo constants (unevaluated form)."

SuperLie`Poisson`ContactAlgebra::usage = 
  "ContactAlgebra[name, x, t] defines a Lie (super)algebra \"name\" as the
algebra of the polynomials of x[1],... ,x[n], t. with standard Contact 
bracket. The Poisson bracket is also defined. ContactAlgebra[name, {p1,...}, t]
and ContactAlgebra[name, x, t, form] defines non-standard Contact and Poisson
brackets."

SuperLie`Poisson`Kb::usage = "Kb[x,y] is the Contact bracket (operator).";
SuperLie`Poisson`kb::usage = "kb[x,y] is the Contact bracket (unevaluated form)."


SuperLie`Poisson`HamiltonianH::usage =
 "HamiltonianH[alg] is the operator from functions to vector fields (implemented
as differential operators) associated with the Poisson algebra alg."

SuperLie`Poisson`\[CapitalDelta]::usage =
 "\[CapitalDelta][alg] is the Laplacian in the algebra alg"

SuperLie`Poisson`EulerOp::usage =
 "EulerOp[alg] is the Euler operator in algebra alg"

SuperLie`Poisson`ContactK::usage =
 "ContactK[alg] is the operator from functions to vector fields (implemented
as differential operators) associated with the breaket in the Contact algebra."

SuperLie`Poisson`ButtinAlgebra::usage = 
  "ButtinAlgebra[name, {x,y}] defines a Buttin (super)algebra \"name\" as the algebra of
the polynomials on x1,x2,...,y1,y2,... with standard Buttin bracket."

SuperLie`Poisson`Bb::usage = "Bb[x,y] is the Buttin bracket (operator).";
SuperLie`Poisson`bb::usage = "bb[x,y] is the Buttin bracket (unevaluated form)."

SuperLie`Poisson`LeitesAlgebra::usage =
  "LeitesAlgebra[name, {x,y}] defines a Leites (super)algebra \"name\" as the algebra of
the polynomials on x1,x2,...,y1,y2,... with standard Schouten antibracket."

SuperLie`Poisson`Sb::usage = "Sb[x,y] is the Schouten antibracket in Leites algebra (operator).";
SuperLie`Poisson`sb::usage = "sb[x,y] is the Schouten antibracket in Leites algebra (unevaluated form)."

SuperLie`Poisson`OKAlgebra::usage = 
  "OKAlgebra[name, {x,y,t}] defines an \"odd\" contact (super)algebra \"name\" as the algebra of
the polynomials on x1,x2,...,y1,y2,... and t with standard bracket."

SuperLie`Poisson`Ob::usage = "Ob[x,y] is the odd Contact bracket (operator).";
SuperLie`Poisson`ob::usage = "ob[x,y] is the odd Contact bracket (unevaluated form)."

SuperLie`Poisson`MoebiusAlgebra::usage = 
  "MoebiusAlgebra[g, {x,\[Theta],t}] defines a Moebius-Poisson superalgebra g as the
algebra of the polynomials on x1,...xn,\[Theta], and t. The x may be also a list of
components, as in PoissonAlgebra."

SuperLie`Poisson`Mb::usage = "Mb[x,y] is the Moebius bracket (operator).";
SuperLie`Poisson`mb::usage = "mb[x,y] is the Moebius bracket (unevaluated form)."

SuperLie`Poisson`RamondAlgebra::usage = 
  "RamondAlgebra[g, {x,\[Theta],t}] defines a Ramond superalgebra g as the algebra of
the polynomials on x1,...xn,\[Theta], and t. The x may be also a list of components,
as in PoissonAlgebra."

SuperLie`Poisson`Rb::usage = "Rb[x,y] is the Ramond bracket (operator).";
SuperLie`Poisson`rb::usage = "rb[x,y] is the Ramond bracket (unevaluated form)."

SuperLie`Poisson`RamondD
SuperLie`Poisson`ZRamondD

SuperLie`Poisson`RamondK::usage =
 "RamondK[alg] is the operator from functions to vector fields (implemented
as differential operators) associated with the breaket in the Ramond algebra."

SuperLie`Poisson`NewBrace::usage =
 "NewBrace[Op, txt] defines new braket Op[f,g] = {f,g}_txt.
 NewBrace[Op, txt, p, op] defines also the unevaluated form op and the parity p."


(* ===== Private section ====== *)

Begin["$`"]

ptrnAux[spaces_, opts_]:=
  Module[{ptrn},
    ptrn=Flatten[{BasisPattern/@spaces, Variables/.opts/.Variables->{}}];
    If[Length[ptrn]==1, ptrn[[1]], Alternatives@@ptrn]]

ptrnPoly[ptrn_] := Flatten[_VTimes|_VPower|ptrn];


NewBrace[Op_, txt_, p_:0, op_:None] :=
 (SetProperties[If[op===None, Op, {Op, op}], {Vector, Vector->__, Linear,
 	Output->ArgForm["{``,``}"], 
        Traditional->SeqForm[
		SequenceForm["{", #1,",\[ThinSpace]", #2, "}", Subscript[txt]]],
	TeX->SeqForm["\\left\\{",#1,",\\,",#2, "\\right\\}_{",txt,"}"] }];
  P[Op] ^= p;
  P[Op[x_,y_]] ^:= pPlus[P[x],P[y],p];
  Parity[Op[x_,y_]] ^:= pPlus[Parity[x],Parity[y],p];
  If[op=!=None,
    P[op] ^= p;
    P[op[x_,y_]] ^:= pPlus[P[x],P[y],p];
    Parity[op[x_,y_]] ^:= pPlus[Parity[x],Parity[y],p]])

(* Parity Sum *)

mod2[n_Number] := Mod[n,2]
mod2[n_] := n


(* HamiltonianH *)

Format[HamiltonianH[Pb_][f_],TraditionalForm]:= HoldForm[Subscripted[H[f]]]

(* \[CapitalDelta] *)

\[CapitalDelta][alg_][f_] := 
  If[$p==2,
   VPlus[ f, SVTimes[-1, EulerOp[alg,2][f]] ],
   VPlus[ SVTimes[2,f], SVTimes[-1, EulerOp[alg][f]] ]]

Format[\[CapitalDelta][alg_],TraditionalForm]:= HoldForm[\[CapitalDelta]]

(* EulerOp *)

Format[EulerOp[alg_],TraditionalForm] := HoldForm[E]

(* ContactK *)

Format[ContactK[alg_][f_],TraditionalForm]:= HoldForm[Subscripted[K[f]]]

(* ====== PoissonAlgebra ======== *)

NewBrace[Pb, "p.b.", 0, pb]

Jacobi[Pb->CircleTimes]


(* Poisson Algebra, the case of  single component and standard form *)

PoissonAlgebra::dim = "The dimension of `` should be even";
PoissinAlgebra::parity = "The elements `` and `` should have equal parities";

PoissonAlgebra[name_, x_Symbol, opts___Rule] :=
  With[{n=Dim[x],n1=Dim[x]+1,k=Dim[x]/2, Pb$l=Pb/.{opts}, pb$l=pb/.{opts},
	sqr = Squaring/.{opts}/.Squaring:>($p===2),
        ptrn=ptrnAux[{x},{opts}],
        EulerOp$l=EulerOp/.{opts}, HamiltonianH$l=HamiltonianH/.{opts}},
    SetProperties[name, { Vector, BasisPattern->ptrnPoly[ptrn],
			Bracket->Pb$l, bracket->pb$l, TheSpace->x, opts} ];
    If[NumberQ[n],
	If [OddQ[n],
	    Message[PoissonAlgebra::dim, x]; Return[$Failed]];
	Do[
	  If[ P[x[i]] != P[x[n1-i]],
	     Message[PoissonAlgebra::parity, x[i], x[n1-i]]; Return[$Failed]],
	  {i,1,k}]
	];
    PolyPattern[name]^=ptrn;
    Pb$l[f_,g_] := 
      VSum[
        SVTimes[-(-1)^P[f],VTimes[LDer[f,x[i],ptrn], LDer[g,x[n1-i],ptrn]]]~VPlus~
        SVTimes[(-1)^(P[f]+P[x[i]]),VTimes[LDer[f,x[n1-i],ptrn],LDer[g,x[i],ptrn]]],
        {i,1,k}];
    HamiltonianH$l[name][f_] :=
      VSum[
        SVTimes[(-1)^P[f],VTimes[LDer[f,x[i],ptrn], ZLDer[x[n1-i],ptrn]]]~VPlus~
        SVTimes[-(-1)^(P[f]+P[x[i]]),VTimes[LDer[f,x[n1-i],ptrn],ZLDer[x[i],ptrn]]],
        {i,1,k}];
    EulerOp$l[name] :=
	VSum[ VTimes[x[i], ZLDer[x[i],ptrn]], {i,1,n}];
    If [sqr,
       Squaring[f_,Pb$l] := VSum[VTimes[LDer[f,x[i],ptrn], LDer[f,x[n1-i],ptrn]],{i,1,k}];
       EulerOp$l[name,2] := VSum[ VTimes[x[i], ZLDer[x[i],ptrn]], {i,1,k}];
    ];
  (* 011215: added enumeration and Basis[g, d] *)
     ReGrade[name, glist_] ^:= (ReGrade[x, glist]; ReGrade[name]);
     name/: ReGrade[name, gr_Integer] := ReGrade[name, poReGList[Basis[x],gr]];
     ReGrade[name] ^:= calcPoBasis[name, x, VTimes, opts];
     ReGrade[name];
    name::usage ^= SPrint["`` is a Poisson algebra over ``", name, x]
 ]


ReGrade::invalid = "The grading `` is invalid or not implemented. The standard grading is used";

poReGlist[basis_,r_] :=
 Module[{gl, n},
   n = Plus @@ (P/@basis);
   Which[
     r==0, Homogen,
	 -n<=r<=n, gl = vectReGlist[Take[basis,Length[basis]/2], r];
	           Join[gl,2-Reverse[gl]],
     True, Message[ReGrade::invalid, r];
           Homogen]]


poBasis[x_, vt_, d_, min_, max_] :=
  Flatten[Table[Outer[ct, GradeBasis[d - i, Basis[x], vt], Basis[dx, i]], {i, min, max}]]

calcPoBasis[g_, x_, vt_, opts___Rule] :=
  Module[{d, b, i, xi, gi, x0, xn, enum, vars, mg},
    enum=KeyValue[{opts}, Enum];
    vars=KeyValue[{opts},Variables,{}];
    If[ListQ[x],
      b = Join@@Basis/@x;
      x0 = x[[1]][1];
      xn = x[[-1]][1],
    (*else*)
      b = Basis[x];
      x0 = x[1];
      xn = x[Dim[x]]];
    b = Join[vars, b];
    d = Length[b];
    For[i = 1, i <= d, i++,
      xi = b[[i]];
      gi = Grade[xi];
      If[! IntegerQ[gi] || gi < 0 || gi == 0 && P[xi] =!= 1, 
        Return[$Failed]]];
    With[{bs=b, dg=Grade[x0]+Grade[xn],sel=KeyValue[{opts}, Select, #=!=0&]}, 
      mg=dg; Do[mg=Max[mg,Grade[vars[[i]]]],{i,1,Length[vars]}];
      If[ enum =!= False,
	   EnumSet[g,  { -mg, Infinity, 1 } -> { d_ :> Basis[g,d]}]];
      Basis[g, d_] ^:= Select[GradeBasis[d+dg, bs, vt],sel]]]

hamSelect[x_]:=Not[x===0 || x===VTimes[]];

(* Poisson Algebra, the case of  single component and user-defined form *)

PoissonAlgebra::form = "Wrong element `` in \"form\" argument";

PoissonAlgebra[name_, x_Symbol, form_List, opts___Rule] :=
  With[{n=Dim[x],nf=Length[form], Pb$l=Pb/.{opts}, pb$l=pb/.{opts},
        ptrn=ptrnAux[{x},{opts}],
	sqr = Squaring/.{opts}/.Squaring:>($p===2),
        EulerOp$l=EulerOp/.{opts}, HamiltonianH$l=HamiltonianH/.{opts}},
    SetProperties[name, { Vector, BasisPattern->ptrnPoly[ptrn],
			Bracket->Pb$l, bracket->pb$l, TheSpace->x, opts} ];
	Do[
	  If[Length[form[[i]]]=!=3 || !IntegerQ[form[[i,2]]] || !IntegerQ[form[[i,3]]],
	     Message[PoissonAlgebra::form, form[[i]]]; Return[$Failed]];
	  If[ P[x[form[[i,2]]]] != P[x[form[[i,3]]]],
	     Message[PoissonAlgebra::parity, x[form[[i,2]]], x[form[[i,3]]]]; Return[$Failed]],
	  {i,1,nf}];
    PolyPattern[name]^=ptrn;
    HamiltonianH$l[name][f_][g_] := SVTimes[-1, Pb$l[f,g]];
    Pb$l[f_,g_] :=
	  Evaluate[VSum[SVTimes[-(-1)^P[f]*form[[i,1]],
	       
VTimes[LDer[f,x[form[[i,2]]],ptrn],LDer[g,x[form[[i,3]]],ptrn]]],
	       {i,1,nf}]];
    HamiltonianH$l[name][f_] :=
	  Evaluate[VSum[SVTimes[(-1)^P[f]*form[[i,1]],
	       
VTimes[LDer[f,x[form[[i,2]]],ptrn],ZLDer[x[form[[i,3]]],ptrn]]],
	       {i,1,nf}]];
    EulerOp$l[name] :=
	VSum[ VTimes[x[i], ZLDer[x[i],ptrn], {i,1,n}]];
    name::usage ^= SPrint["`` is a Poisson algebra over ``", name, x]
  ]

(* Poisson Algebra, the case of  list of components *)

PoissonAlgebra::dims = "The dimensions of `` and `` should be equal";
PoissonAlgebra::even = "The element `` should be odd";

PoissonAlgebra[name_, {x__}, opts___Rule] :=
 With[{Pb$l=Pb/.{opts}, pb$l=pb/.{opts},  ptrn=ptrnAux[{x},{opts}],
       EulerOp$l=EulerOp/.{opts}, HamiltonianH$l=HamiltonianH/.{opts},
       sqr = Squaring/.{opts}/.Squaring:>($p===2)},
  Module[{r, n, k, k1, m, parlist, idx, nind, v, x1, x2, err=False, px, rule, dd},
    Vector[v];
      r = Length[{x}];
      n = Dim /@ {x};
      k = Floor[r/2];
      k1 = If[OddQ[r],k+1,0];
    SetProperties[name, { Vector, BasisPattern->ptrnPoly[ptrn],
        Bracket->Pb$l, bracket->pb$l, opts} ];
	(* Check the dimensions of components correspondence of parities *)
	Do[j=r+1-i;
	   x1 = {x}[[i]];
	   x2 = {x}[[j]];
	   If[n[[i]]!=n[[j]],
	     Message[PoissonAlgebra::dims, n[[i]], n[[j]]]; Return[$Failed]];
	   Do[If[ P[x1[l]] != P[x2[l]],
	     Message[PoissonAlgebra::parity, x1[l], x2[l]]; Return[$Failed]],
		 {l, 1, n[[i]]}],
	   {i,1,k}];
	If[k1>0,
	   x1 = {x}[[k1]];
	   Do[If[ P[x1[l]] != 1,
	      Message[PoissonAlgebra::even, x1[l]]; Return[$Failed]],
	   {l, 1, n[[k1]]}]];
    PolyPattern[name]^= ptrn;
    rule =
     (HoldPattern[Pb$l[f_, g_]] :>
        Evaluate[VPlus[
	  VSum[
	    With[{x1={x}[[i]], x2={x}[[r+1-i]], d=dd[i]},
	      VSum[Evaluate @
	        VPlus[
	          SVTimes[(-1)^(P[f]P[x1[l]]),
	             VTimes[LDer[f,x1[l],ptrn], LDer[g,x2[l],ptrn]]],
		  SVTimes[-(-1)^((P[f]+1)P[x1[l]]),
		     VTimes[LDer[f,x2[l],ptrn], LDer[g,x1[l],ptrn]]]],
		{l,1,d}]],
	    {i,1,k}],
	  VIf[k1>0,
	    With[{x1 = {x}[[k1]],d=dd[k1]},
	      VSum[Evaluate @
		SVTimes[(-1)^P[f], VTimes[LDer[f,x1[l],ptrn], LDer[g,x1[l],ptrn]]],
		{l,1,d}]]]
	    ]]);
    SetDelayed @@ (rule /. Table[dd[i]->n[[i]],{i,1,r}]);
    rule =
     (HoldPattern[HamiltonianH$l[name][f_]] :>
        Evaluate[VPlus[
	  VSum[
	    With[{x1={x}[[i]], x2={x}[[r+1-i]], d=dd[i]},
	      VSum[Evaluate @
	        VPlus[
	          SVTimes[-(-1)^(P[f]P[x1[l]]),
	             VTimes[LDer[f,x1[l],ptrn], ZLDer[x2[l],ptrn]]],
		  SVTimes[(-1)^((P[f]+1)P[x1[l]]),
		     VTimes[LDer[f,x2[l],ptrn], ZLDer[x1[l],ptrn]]]],
		{l,1,d}]],
	    {i,1,k}],
	  VIf[k1>0,
	    With[{x1 = {x}[[k1]],d=dd[k1]},
	      VSum[Evaluate @
		SVTimes[-(-1)^P[f], VTimes[LDer[f,x1[l],ptrn], ZLDer[x1[l],ptrn]]],
		{l,1,d}]]]
	    ]]);
    SetDelayed @@ (rule /. Table[dd[i]->n[[i]],{i,1,r}]);
    EulerOp$l[name] :=
      Evaluate[VSum[
		 With[{x1={x}[[i]], d=n[[i]]},
	       Unevaluated[VSum[ VTimes[x1[l], ZLDer[x1[l],ptrn]], {l,1,d}]]],
		 {i,1,r}]];
    If [sqr,
    rule =
     (HoldPattern[Squaring[f_,Pb$l]] :>
        Evaluate[VPlus[
	  VSum[
	    With[{x1={x}[[i]], x2={x}[[r+1-i]], d=dd[i]},
	      VSum[Evaluate @ VTimes[LDer[f,x1[l],ptrn], LDer[f,x2[l],ptrn]], {l,1,d}]],
	    {i,1,k}]
	(*,  VIf[k1>0,
	    With[{x1 = {x}[[k1]],d=dd[k1]},
	      VSum[Evaluate @ VTimes[LDer[f,x1[l],ptrn], LDer[g,x1[l],ptrn]]], (* not yet *)
		{l,1,d}]] *)
	    ]]);
        SetDelayed @@ (rule /. Table[dd[i]->n[[i]],{i,1,r}]);
        EulerOp$l[name,2] := Evaluate[VSum[
		 With[{x1={x}[[i]], d=n[[i]]},
	       Unevaluated[VSum[ VTimes[x1[l], ZLDer[x1[l],ptrn]], {l,1,d}]]],
		 {i,1,r/2}]];
    ];
  (* 011215: added enumeration and Basis[g, d] *)
     name/: ReGrade[name, gr_Integer] := (poReGradeM[{x}, gr]; ReGrade[name]);
     ReGrade[name] ^:= calcPoBasis[name, {x}, VTimes, opts];
     ReGrade[name];
   name::usage ^= SPrint["`` is a Poisson algebra over ``", name, {x}]
  ]
 ]

poReGradeM[x_,r_] :=
 Module[{i, j, xi, xj, bsi, k, gl, sgn=1, rt=r},
   If [r<0,	 x = poRev[x]; sgn = -1; rt = -r];
   For[i=1;j=Length[x], i<j, i++;j--,
     xi = x[[i]];
	 xj = x[[j]];
	 n = PDim[xi][[1]];
	 If[n==0 || r==0,
	    ReGrade[xi, Homogen];
		ReGrade[xj, Homogen],
	  (*else*)
		ri = Min[rt, n];
	    rt -= ri;
	    gl = vectReGlist[basis[xi], sgn*ri];
		ReGrade[xi, gl];
		ReGrade[xj, 2-gl]]]]

poRev[x_] :=
  Module [{l,q, x1, x2},
    l = Length[x];
    q = Floor[l/2];
	x1 = Reverse[Take[x, q]];
	x2 = Reverse[Take[x, -q]];
    Join[x1, If[EvenQ[l], {}, {x[[q+1]]}], x2]] 


(* ======== Hamilton Algebra ========== *)

NewBrace[Hb, "H.b.", 0, hb]

HamiltonAlgebra[name_, x_, opts___Rule] :=
  With[{Hb$l=Hb/.{opts}, hb$l=hb/.{opts}, Pb$l=Pb/.{opts}},
    PoissonAlgebra[name, x, opts];
	Hb$l[f_, g_] := Pb$l[f, g] /. e_VTimes :> 0 /; Length[e] == 0;
    Bracket[name] ^= Hb$l;
	bracket[name] ^= hb$l;
     ReGrade[name] ^:= calcPoBasis[name, x, VTimes, Select->hamSelect, opts];
     ReGrade[name];
	name::usage ^= SPrint["`` is a Hamiltonian algebra over ``", name, x]
  ]

HamiltonAlgebra[name_, x_Symbol, form_List, opts___Rule] :=
  With[{Hb$l=Hb/.{opts}, hb$l=hb/.{opts}, Pb$l=Pb/.{opts}},
    PoissonAlgebra[name, x, form, opts];
	Hb$l[f_, g_] := Pb$l[f, g] /. e_VTimes :> 0 /; Length[e] == 0;
    Bracket[name] ^= Hb$l;
	bracket[name] ^= hb$l;
     ReGrade[name] ^:= calcPoBasis[name, x, VTimes, Select->hamSelect, opts];
     ReGrade[name];
	name::usage ^= SPrint["`` is a Hamiltonian algebra over ``", name, x]
  ]

(* ======== Contact Algebra ========== *)

NewBrace[Kb, "k.b.", 0, kb]

Jacobi[Kb->CircleTimes]

ContactAlgebra[name_, x_, t_, opts___] :=
 With[{Kb$l=Kb/.{opts}, kb$l=kb/.{opts}, Pb$l=Pb/.{opts}, ContactK$l=ContactK/.{opts},
       EulerOp$l=EulerOp/.{opts}, HamiltonianH$l=HamiltonianH/.{opts},
       sqr = Squaring/.{opts}/.Squaring:>($p===2)},
  Module[{n=Dim[x], fm=form, m, parlist, idx, nind, v, ptrn},
    TrivialSpace[t];
    If[
      PoissonAlgebra[name, x, Variables->Join[{t},Variables/.{opts}/.Variables->{}], opts]
      ===$Failed, Return[$Failed]];
(*  BasisPattern[name] ^= BasisPattern[name] | t;      *)
(*  PolyPattern[name] ^= ptrn = PolyPattern[name] | t; *)
    ptrn = PolyPattern[name];
    ContactK$l[name][f_] := VPlus[
       VTimes[\[CapitalDelta][name][f], ZLDer[t,ptrn]],
       SVTimes[-1, HamiltonianH$l[name][f]],
(*     HamiltonianH[name][f],  *)
       VTimes[LDer[f,t,ptrn], EulerOp$l[name]]];
    Kb$l[f_,g_] := VPlus[
	   VTimes[\[CapitalDelta][name][f], LDer[g,t,ptrn]],
	   SVTimes[-1, VTimes[LDer[f,t,ptrn], \[CapitalDelta][name][g]]],
(*	   SVTimes[-1, Pb$l[f,g]]];  *)
	   Pb$l[f,g]];
    If[sqr,
       Squaring[f_,Kb$l] := VPlus[
	   VTimes[\[CapitalDelta][name][f], LDer[f,t,ptrn]],
	   Squaring[f,Pb$l]]];
    Bracket[name] ^= Kb$l; 
    bracket[name] ^= kb$l; 
    name::usage ^= SPrint["`` is a Contact algebra over `` and ``", name, x, t]
 ]
]

(* ======= Buttin Algebra ========= *)

NewBrace[Bb, "b.b.", 1, bb]

(* Le[f_][g_] := Bb[f,g] *)

ButtinAlgebra::dims = PoissonAlgebra::dims;
ButtinAlgebra::parity = "The elements `` and `` should have different parity";


ButtinAlgebra[name_, {x_,y_}, opts___Rule] :=
  With[{n=Dim[x], Bb$l=Bb/.{opts}, bb$l=bb/.{opts},
     sqr = Squaring/.{opts}/.Squaring:>($p===2),
     EulerOp$l=EulerOp/.{opts}, ptrn=ptrnAux[{x,y},{opts}]},
    SetProperties[name, { Vector, BasisPattern->ptrnPoly[ptrn],
			Bracket->Bb$l, bracket->bb$l, opts} ];
    If[Dim[y]=!=n,
      Message[ButtinAlgebra::dims, x, y]; Return[$Failed]];
    If[NumberQ[n],
      Do[If[ PolynomialMod[P[x[i]]-P[y[i]], 2]=!=1,
           Message[ButtinAlgebra::parity, x[i], y[i]]; Return[$Failed]],
        {i,1,n}]];
    PolyPattern[name]^=ptrn;
    If [sqr,
      Squaring[f_,Bb$l] := VIf[P[f]==0,VSum[VTimes[LDer[f,x[i],ptrn],LDer[f,y[i],ptrn]]],{i,1,n}]];
    Bb$l[f_,g_] := 
      VSum[
        SVTimes[(-1)^(P[f]P[x[i]]),VTimes[LDer[f,x[i],ptrn],LDer[g,y[i],ptrn]]]~VPlus~
        SVTimes[(-1)^(P[f]P[y[i]]),VTimes[LDer[f,y[i],ptrn],LDer[g,x[i],ptrn]]],
        {i,1,n}];
    EulerOp$l[name] ^:=
	 VSum[ VTimes[x[i], ZLDer[x[i],ptrn]], {i,1,n}]~VPlus~
	 VSum[ VTimes[y[i], ZLDer[y[i],ptrn]], {i,1,n}];
  (* 011215: added enumeration and Basis[g, d] *)
     ReGrade[name] ^:= calcPoBasis[name, {x,y}, VTimes, opts];
     ReGrade[name];
    name::usage ^= SPrint["`` is a Buttin algebra over ``", name, {x, y}]
]

(* ======= Leites Algebra ========= *)

NewBrace[Sb, "S.b.", 1, sb]

(* Le[f_][g_] := Bb[f,g] *)

LeitesAlgebra::dims = PoissonAlgebra::dims;
LeitesAlgebra::parity = "The elements `` and `` should have different parity";

LeitesAlgebra[name_, x_, opts___Rule] :=
  With[{Sb$l=Sb/.{opts}, sb$l=sb/.{opts}, Bb$l=Bb/.{opts}},
    ButtinAlgebra[name, x, opts];
	Sb$l[f_, g_] := Bb$l[f, g] /. e_VTimes :> 0 /; Length[e] == 0;
    Bracket[name] ^= Sb$l;
    bracket[name] ^= sb$l;
    ReGrade[name] ^:= calcPoBasis[name, x, VTimes, Select->hamSelect, opts];
    ReGrade[name];
    name::usage ^= SPrint["`` is a Leites algebra over ``", name, x]
  ]


(* ======= "Odd" Contact Algebra ========= *)

NewBrace[Ob, "m.b.", 1, ob]

OKAlgebra[name_, {x_, y_, t_}, opts___Rule] :=
 With[{Ob$l=Ob/.{opts}, ob$l=ob/.{opts}, Bb$l=Bb/.{opts},
   EulerOp$l=EulerOp/.{opts}, 
   vars=Join[{t},Variables/.{opts}/.Variables->{}]},
  Module[{n=Dim[x], fm=form, m, parlist, idx, nind, v, ptrn},
    TrivialSpace[t,1];
    If[ ButtinAlgebra[name, {x,y}, Variables->vars, opts]==$Failed,  Return[$Failed]];
(*  BasisPattern[name] ^= BasisPattern[name] | t;  *)
(*  PolyPattern[name] ^= ptrn = PolyPattern[name] | t;  *)
    ptrn = PolyPattern[name];
(*
    ContactK[f_] := VPlus[
       VTimes[\[CapitalDelta][name][f], ZLDer[t,ptrn]],
       SVTimes[-1, HamiltonianH[name]f]],
	   VTimes[LDer[f,t,ptrn], EulerOp$l[name]]];
*)
    Ob$l[f_,g_] := VPlus[
	   VTimes[\[CapitalDelta][name][f], LDer[g,t,ptrn]],
	   SVTimes[(-1)^P[f], VTimes[LDer[f,t,ptrn], \[CapitalDelta][name][g]]],
	   SVTimes[-1, Bb$l[f,g]]];
	Bracket[name] ^= Ob$l;
	bracket[name] ^= ob$l;
    name::usage ^= SPrint["`` is an \"odd\" contact algebra over ``", name, {x, y, t}]
  ]  
]


(* ======= Moebius-Poisson Algebra ========= *)

NewBrace[Mb, "MP.b.", 0, mb]

(* Le[f_][g_] := Bb[f,g] *)

MoebiusAlgebra[name_, {x_, th_, t_}, opts___Rule] :=
 With[{Mb$l=Mb/.{opts}, mb$l=mb/.{opts}, Pb$l=Pb/.{opts},
   vars=Join[{t,th},Variables/.{opts}/.Variables->{}],
   EulerOp$l=EulerOp/.{opts}},
  Module[{n=Dim[x], fm=form, m, parlist, idx, nind, v, ptrn, poissonEulerOp},
    TrivialSpace[t];
    TrivialSpace[th,1];
    If[PoissonAlgebra[name, x, Variables->vars, EulerOp->poissonEulerOp, opts]==$Failed,
      Return[$Failed]];
    ptrn = PolyPattern[name];
    EulerOp$l[name]^=VPlus[poissonEulerOp[name],
    			 SVTimes[1, VTimes[th,ZLDer[th,ptrn]]]];
    Mb$l[f_,g_] :=
     VPlus[Pb$l[f,g],
    	   SVTimes[(-1)^P[f],VTimes[VPower[t,-1],LDer[f,th,ptrn],LDer[g,th,ptrn]]]];
    Bracket[name] ^= Mb$l; 
    bracket[name] ^= mb$l; 
    name::usage ^= SPrint["`` is a Moebius-Poisson algebra over ``", name, {x, th, t}]
 ]
]


(* ======= Ramond Algebra ========= *)

NewBrace[Rb, "R.b.", 0, rb]

RamondAlgebra[name_, {x_, th_, t_}, opts___Rule] :=
 With[{Rb$l=Rb/.{opts}, rb$l=rb/.{opts}, Mb$l=Mb/.{opts}, EulerOp$l=EulerOp/.{opts}},
  Module[{n=Dim[x], fm=form, m, parlist, idx, nind, v, ptrn, possonH},
    If[ MoebiusAlgebra[name, {x, th, t}, HamiltonianH->poissonH, opts]==$Failed, 
      Return[$Failed]];
    ptrn = PolyPattern[name];
    HamiltonianH[name][f_] := VPlus[
      poissonH[name][f],
      SVTimes[-(-1)^P[f], VTimes[VPower[t,-1], LDer[f,th,ptrn], ZLDer[th,ptrn]]]];
    RamondK[name][f_] := VPlus[
       VTimes[\[CapitalDelta][name][f], ZRamondD[t,th,ptrn]],
       SVTimes[-1, HamiltonianH[name][f]],
       VTimes[RamondD[f,t,th,ptrn], EulerOp$l[name]]];
    Rb$l[f_,g_] := VPlus[
	   VTimes[\[CapitalDelta][name][f], RamondD[g,t,th,ptrn]],
	   SVTimes[-1, VTimes[RamondD[f,t,th,ptrn], \[CapitalDelta][name][g]]],
	   SVTimes[-1, Mb$l[f,g]]];
    name::usage ^= SPrint["`` is a Ramond algebra over ``", name, {x, th, t}]
  ]  
]

RamondD[f_, t_, th_, ptrn_] := VPlus[
  LDer[f,t,ptrn],
  SVTimes[-1/2, VTimes[th,VPower[t,-1],LDer[f,th,ptrn]]]];
  
Vector[ZRamondD];
ZRamondD[t_,th_,ptrn_][f_] := RamondD[f, t, th, ptrn];

Unprotect[OrderedQ]
OrderedQ[{___,_ZRamondD,__}]=False
OrderedQ[{x___,_ZRamondD}]:=OrderedQ[{x}]
Protect[OrderedQ]

Format[HoldPattern[ZRamondD[__]]] := "\[ScriptCapitalD]"



End[]
EndPackage[]

