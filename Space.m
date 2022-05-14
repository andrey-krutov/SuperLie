BeginPackage["SuperLie`Space`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`"}]

VectorSpace::usage = 
  "VectorSpace[name, Dim->dim] - define space \"name\" with dimension \"dim\" .
 For superspace dim = {d1, d2, .. } - d1 even components, d2 odd, d3 even, ...";

ReGrade::usage = 
  "ReGrade[x, {g1,...}] changes the grading of the space x and all known relatives.
ReGrade[x, gradingName] changes the grading of x to the named special grading.";

TrivialSpace::usage = 
  "TrivialSpace[name] - define space \"name\" with dimension 1 and basis {name}.
 TrivialSpace[name,1] define trivial odd space";

Options[VectorSpace] ^=
  { Output->Subscripted, TeX->Subscripted, Standard->Subscripted,
    Traditional->Subscripted, Enum->Auto }
Options[Algebra] ^= { Bracket->Act }

SpacePlus::usage = 
  "SpacePlus[name, {term,...}] - define space \"name\" as a direct sum of the terms";

NewRelative::usage =
  "NewRelative[rel, old->new] - attach a new relative to the family of modules.
The first argument is the relation of \"new\" to \"old\" : MLeft (the same),
CoLeft, MRight, CoRight, PiRight, DLeft, PiLeft, DRight."

{ MLeft, CoLeft, MRight, CoRight, PiRight, DRight, PiLeft , DLeft }

GetRelative::usage =
  "GetRelative[v, relation] returns the relative space to v. If no relative defined,
creates a new one (asks the user about the name)"

PiLeft::usage = 
 "PiLeft[md->pimd] builds the module \"pimd\" as pi*md, where \"pi\" is
1-dimensional trivial odd module."

PiRight::usage = 
 "PiRight[md->mdpi] builds the module \"mdpi\" as md*pi, where \"pi\" is
1-dimensional trivial odd module."

MRight::usage = 
 "MRight[md->altmd] builds the module \"altmd\" as pi*md*pi, where \"pi\" 
is 1-dimensional trivial odd module."

CoLeft::usage =
 "CoLeft[md->comd] builds the module \"comd\" on the space of left even
linear form on \"md\". The function is implemented only for finite-dimensional
modules with one-indexed basis."

DLeft::usage =
 "DLeft[md->dmd] builds the module \"dmd\" on the space of left odd linear
form on \"md\".  If md is an algebra, DLeft defines also the exterior derivative
Der : dmd -> dmd/\\dmd."

Options[NewRelative] ^=
  {Output->Auto, TeX->Auto, Standard->Auto, Traditional->Auto}

SubSpace::usage = 
 "SubSpace[name, in, basis] - define a subspace with given basis."

Algebra::usage = 
  "(A) Algebra[x, options] defines vector space and algebra \"x\".
The operation on x should be defined explicitly.
(B) Algebra->name is an option for some constructors."

CommutativeLieAlgebra::usage = 
  "CommutativeLieAlgebra[x] defines on space \"x\" a Lie bracket 
[x[..], x[..]] = 0."

Enum::usage = Enum::usage <>
 "Enum->mode is the optional parameter for VectorSpace function. It sets
the mode of the enumeration of the basis of the space.
Enum->False suppresses the enumeration."

Relatives::usage = 
  "Relatives[x] (x is a module) is the list of relative spaces :\n
{MLeft (x itself), CoLeft, MRight, CoRight, PiRight, DRight, PiLeft, DLeft}."

TheSpace::usage =
  "For any space name or other symbol \"x\", TheSpace[x] is the name of
original space from which \"x\" is derived."

InSpace::usage =
  "InSpace[subspace] in the name of the space where the subspace lies."

Basis::usage =
 "Basis[space] returns the basis of the space. Basis[space,d] returns the
 basis of the d-th grade component of the space."

BasisPattern::usage =
 "BasisPattern[space] is the pattern for basis of this space."

Image::usage =
 "Image[g] is the list of images of basis elements of \"g\" if \"g\" is
defined as a subspace.";

PList::usage =
 "PList->{...} is the optional parameter for VectorSpace function. It is
the list of parities of the vectors forming basis of new space."

GList::usage =
 "GList->{...} is the optional parameter of Space Constructor functions. It is
the list of degrees of generators of new space."

WList::usage =
 "WList->{...} is the optional parameter of Space Constructor functions. It is
the list of weights of generators of new space."

TheAlgebra::usage =
  "TheAlgebra[m] is the name of the algebra acting on the module m."

TheModule::usage =
  "TheModule[v] is the name of the module hosting the vector v."

(* $Algebra::usage = "$Algebra - current default algebra." *)

(* $Module::usage = "$Module - current default module." *)

Components::usage =
 "For modules with regular Lie operation Components[m] is the list or
regular components."

MappingRule::usage=
"MappingRule[U,V] returns the rule of mapping U->V.
 Use LinearChange[u,MappingRule[U,V]] to implement the mapping. See also Mapping option."

Mapping::usage=
"The option Mapping->fn instructs the sub- and factorspace constructors to define fn as
 mapping function (immersion or projection)."


Begin["$`"]

(*******************************************]
 *
 *	 Vector Spaces Constructors
 *
[*******************************************)


(* --------------- Space properties ---------------- *)

NewValue[BasisPattern, Image, InSpace, TheSpace,
	 Dim, PDim, Relatives, PList, GList, WList, Enum]


(******************* Vector Space **********************)

RelList = { MLeft, CoLeft, MRight, CoRight, PiRight, DRight, PiLeft, DLeft }

VectorSpace[vect_, opts___] :=
  Module [ {ord, adj, name, properties, enum},
   Block[{PiOrder = False},
    If [(Clear /. {opts}) =!= False,
       Clear[vect];
       Relatives[vect] ^= Prepend[Table[None, {7}], vect]];
    properties = Complement[ {opts}, (#->None)& /@ RelList, {Clear->Yes, Algebra}, SameTest -> SameKeysQ];
    properties  = UnionKeys[ properties, Options[VectorSpace] ];
    enum = Enum /. properties;
    properties = Complement[ properties, {Enum}, SameTest -> SameKeysQ];
    SetProperties[ vect, { Vector, BasisPattern->_vect } ];
    SetProperties[ vect,  properties ];
    TheModule[_vect] ^= KeyValue[properties, TheModule, vect];
    If [enum===Auto, EnumSet[vect, {1,1,1}->{dg_:>Array[vect,Dim[vect]]}]];
    Basis[vect, d_] ^:= Select[Basis[vect], Grade[#]==d&];
(*  If[(Standard/.properties) === Subscripted,
	Subscript[vect,i__] ^:= vect[i] ]; *)
    glist = GList /. {opts};
    If [ ListQ[GList[vect]],
       Grade[vect[i_]] ^:= GList[vect][[i]]];
    If [ ListQ[WList[vect]],
       Weight[vect[i_]] ^:= WList[vect][[i]]];
    Do [ name = KeyValue[ {opts}, RelList[[n]] ];
	 If [name, Continue[], Continue[] ];
	 Define[name, { Vector, BasisPattern->_name } ];
	 PiOrder = (n>=4);
	 SetProperties[ name,  properties ];
	 NewRelative[n, vect->name](*;
     If[(Standard/.properties) === Subscripted,
	   With[{nm=name}, Subscript[nm,i__] ^:= nm[i]]]*),
       { n, 2, 8 }
    ];
    vect::usage = SPrint["`` is a vector space", vect]
 ]]


Basis[v_] := EnumList[v];
Basis[v_,deg_] := EnumList[v,Range->deg];


(******************* ReGrade **********************)

ReGrade::undef = "Undefined regrading `` of ``"

ReGrade[v_, Homogen] :=
  (If [ValueQ[GList[v]], v/:GList[v]=.];
   Do[With[{x = Relatives[v][[i]]},
     If[x =!= None,
       If[OddQ[i], Grade[x[i_]] ^:= 1, 
            Grade[x[i_]] ^:= -1]]],
      {i, 1, 8}])

ReGrade[v_, Parity] :=
  (If [ValueQ[GList[v]], v/:GList[v]=.];
   Do[With[{x = Relatives[v][[i]]},
     If[x =!= None,
       If[OddQ[i], Grade[x[i_]] ^:= 1-P[x[i]], 
            Grade[x[i_]] ^:= P[x[i]]-1]]],
      {i, 1, 8}])

ReGrade[v_, glist_] :=
  Module[{},GList[v -> glist];
    Do[With[{x = Relatives[v][[i]]},
        If[x =!= None,
          If[OddQ[i], Grade[x[i_]] ^:= GList[v][[i]], 
            Grade[x[i_]] ^:= -GList[v][[i]]]]],
      {i, 1, 8}]] /;
  ListQ[glist] || (Message[ReGrade::undef, glist, v]; False)


(******************* Trivial Space **********************)

TrivialSpace[vect_, par_Integer:0, opts___Rule] :=
  (VectorSpace[vect, Dim->If[EvenQ[par],1,{0,1}], opts];
   BasisPattern[vect] ^= vect;
   P[vect] ^= If[EvenQ[par],0,1];
   vect[1] = vect
  )


(******************* SpacePlus **********************)

Options[SpacePlus]= { Output->None, TeX->None, Standard->None, Traditional->None}

SpacePlus[vect_, terms_List, opts___Rule] :=
  Module [ {ord, adj, name, properties, enum},
   Block[{PiOrder = False},
    If [(Clear /. {opts}) =!= False, Clear[vect]];
    properties = Complement[ {opts}, (#->None)& /@ RelList, {Clear->Yes}, SameTest -> SameKeysQ];
    properties  = UnionKeys[ properties, Options[SpacePlus], Options[VectorSpace] ];
    enum = Enum /. properties;
    SetProperties[ vect, { Vector, BasisPattern->Flatten[Alternatives@@BasisPattern /@ terms]} ];
    SetProperties[ vect,  properties ];
    Dim[vect] ^= Plus @@ (Dim /@ terms);
    PDim[vect] ^= Plus @@ (PDim /@ terms);
    TheModule[_vect] ^= vect;
    If [enum===Auto, EnumJoin[vect, Sequence@@terms]];
    Relatives[vect] ^= Prepend[Table[None, {7}], vect];
    Do [ name = KeyValue[ {opts}, RelList[[n]] ];
	 If [name, Continue[], Continue[] ];
	 Define[name, { Vector, BasisPattern->_name } ];
	 PiOrder = (n>=4);
	 SetProperties[ name,  properties ];
	 NewRelative[n, vect->name],
       { n, 2, 8 }
    ];
    vect::usage = SPrint["`` is a vector space", vect]
 ]]
 

(******************* SubSpace **********************)
(* 981101: PiOrder->True changes parity *)
(* 001121: Mapping and MappingRule *)

SubSpace[n_, in_, el_, opts___] :=
  Module[{par, dim},
    par = If[TrueQ[Hold[PiOrder]/.{opts}], 1- P /@ el, P /@ el];
    dim = Length[el];
(*
    dim = If [MemberQ[par,1],
            If [MemberQ[par,0], PList->par, Dim->{0,dim}],
	    Dim->dim];
*)
	dim = If [Select[par,#=!=0&,1]=!={},
            If [Select[par,#=!=1&,1]=!={}, PList->par, Dim->{0,dim}],
	    Dim->dim];
    VectorSpace[n, dim, InSpace->in, Image->el, opts];
    Image[n,in]^=el;
    DefMapping[Mapping/.{opts}, n, el];
  ]


DefMapping[fn_,v_,img_]:=
  If[fn=!=Mapping, 
    SetProperties[fn, {Vector,Vector->_}];
    If[!MemberQ[Rules[fn], HoldForm[LinearRule[fn]]], Linear[fn]];
    fn[v[i_]]^:=img[[i]];
    Mapping[v,InSpace[v]]^=fn
  ]


MappingRule[u_,v_] := (u[i_]:>Image[u,v][[i]])/;ValueQ[Image[u,v]]


Mapping[u_,v_][x_] := (x/.u[i_]:>Image[u,v][[i]])/;ValueQ[Image[u,v]]


(******************* SubSubSpace ******************* 001121 *)
(* Let U and V are both defined as subspaces of W.
 * SubSubSpace[U,V,W] redefines U as subspace of V.
 *)

SubSubSpace[u_,v_,w_,opts___Rule]:=
  Module[{spl=Split/.{opts}/.Split->(True&), uim=Image[u,w], vim=Image[v,w],
      wtv, i,j, ui, c, sm, wt, lv, sol, img, fn},
    Scalar[c];
	wtv=spl/@vim;
	lv=Length[vim];
	img=Table[0,{Length[uim]}];
    For[i=1,i<=Length[uim],i++,
	  ui=uim[[i]];
	  wt=spl[ui];
      sm = VSum[ VIf[wtv[[j]] == w, SVTimes[c[j],vim[[j]] ]], {j, 1, lv}];
      sol = SVSolve[v == sm];
      If[sol == {},
        Print[v, "\[NotElement]", p]; Return[$Failed],
      (*else*)
        img[[i]]=VSum[SVTimes[c[j],v[i]], {i, 1, lv}] /. sol[[1]] /. c[_] -> 0]];
	Image[u,v]^=img;
	DefMapping[Mapping/.{opts}, u, v];
	If[(Default/.{opts})=!=False,
	  Image[u]^=img;
	  InSpace[u]^=v];
]


(*************************************************]
 *
 *		Lie Superalgebras 
 *
[*************************************************)

NewValue[Bracket, bracket, BracketMode, TheAlgebra]

bracket[g_ -> Auto, more___] :=
  (bracket[g]^=OpSymbol[Bracket[g]]; bracket[more])

TheModule[v_VPlus] := TheModule[First[v]]
TheModule[v_SVTimes] := TheModule[Last[v]]

TheAlgebra[v_] := None
(*TheAlgebra[v_] := TheAlgebra[TheModule[v]]*)


(******************  Algebra *****************)

Options[Algebra] ^= {Bracket->Act, bracket->Auto}

Algebra[g_, opts___] :=
    (VectorSpace[g, Sequence @@ UnionKeys[{opts,TheAlgebra->g}, Options[Algebra]]];
     g::usage = SPrint["`` is an algebra", g])


(******************  Commutative Lie Algebra *****************)

CommutativeLieAlgebra[g_, opts___] :=
  Module[ { prop, brk},
    Algebra[g,opts];
    prop = UnionKeys[{opts}, Options[Algebra]];
    brk = KeyValue[ prop, Bracket ];
    TheModule[_g] ^= g; 
    brk[v_g, w_g] ^= 0;
 ]


(*******************  NewRelative  *****************)

SubRel[i_,j_] :=
  With[{k=Mod[i-j,4]},
    If[i<=4,
      If[j<=4, k+1, 5+Mod[4-k,4]],
      If[j<=4, k+5, 1+Mod[4-k,4]]]]
(* Mod[i-j,4] + If [Xor[i<=4, j<=4], 4, 0] + 1*)

NewRelative[rel_, old_->new_, opts___Rule] :=
  Module[{i, md, adj, rn, outform, texform, ir},
    adj = Table[None, {8}];
    rn = If [IntegerQ[rel], rel, Position[ RelList, rel ][[1,1]] ];
    Relatives[old] ^= ReplacePart[Relatives[old], None, rn ];
    For [ir=1, ir<=8, ++ir, 
   	md = Relatives[old][[ir]];
	If [md===None, Continue[] ];
	Relatives[md] ^= ReplacePart[ Relatives[md], new, SubRel[rn,ir] ];
	adj = ReplacePart[ adj,  md,  SubRel[ir,rn]];
    ];
    Relatives[old] ^= ReplacePart[Relatives[old], new, rn ];
    If [adj[[4]]=!=None,
	ScalarProduct[new[i_], Evaluate[adj[[4]]] [j_]] ^:= Delta[i-j] ];
    If [ adj[[2]]=!=None,
	ScalarProduct[Evaluate[adj[[2]]][i_], new[j_]] ^:= Delta[i-j] ];
    Relatives[new] ^= adj; 
    {outform, texform, stdform, tradform} =
	 {Output,TeX,Standard,Traditional} /. {opts} /. Options[NewRelative];
    relativeFormat[old, new, outform, OutputForm];
    relativeFormat[old, new, texform, TeXForm];
    relativeFormat[old, new, stdform, StandardForm];
    relativeFormat[old, new, tradform, TraditionalForm];
    If [ IntegerQ[Enum[old]],
	Enum[new] ^= Enum[old];
	If [OddQ[rn],
	  EnumRange[new, i_] ^:= EnumRange[old,i];
	  Enum[new,i_] ^:= Enum[old,i] /. old->new,
	(*else*)
	  EnumRange[new, i_] ^:= - EnumRange[old,i];
	  Enum[new,i_] ^:=
	     If [IntegerQ[#[[1]]], MapAt[Minus, #, 1],
		With[{pt=#[[1,1]]}, #/.{h_Pattern->pt_,pt->-pt}]]& /@
					(Enum[old,i] /. old->new)
	]
    ];
    Vector[new];
    TheModule[_new] ^= new;
    If[ValueQ[TheAlgebra[old]],
      TheAlgebra[new] ^= TheAlgebra[old]];
    If[OddQ[rn],
      Grade[v_new] ^:= Grade[old @@ v];
      Weight[v_new] ^:= Weight[old @@ v],
    (*else*)
      Grade[v_new] ^:= -Grade[old @@ v];
      Weight[v_new] ^:= -Weight[old @@ v]
    ];
    Dim[new] ^= Dim[old];
    If[rn<=4, 	P[new[args___]] ^:= P[old[args]];
		PDim[new] ^= PDim[old],
      (*else*)	P[new[args___]] ^:= 1 - P[old[args]];
		PDim[new] ^= Reverse[PDim[old]]
    ];
    If[Dim[old]<Infinity, Basis[new, d_] ^:= Select[Basis[new], Grade[#]==d&]];
  ]

relativeFormat[old_, new_, format_, ftype_] :=
   SetFormat[ftype, new, format]

relativeFormat[old_, new_, None, ftype_] := Null

relativeFormat[old_, new_, Auto, ftype_] :=
   With[{format=KeyValue[Formats[old], ftype, None]},
     If[format=!=None, SetFormat[ftype, new, format]]];


(********** GetRelative *************)

GetRelative[v_, rel_] :=
  Module[{relfn, relno, relspace},
    Switch[Head[rel],
	  Integer,
	     If[1<=rel<=8,
			relfn = RelList[[rel]]; relno = rel,
			Message[GetRelative::relkey, rel]; Return[$Failed]],
	  Symbol,
	     relno = Position[RelList, rel];
		 If [relno=={},
		      Message[GetRelative::relkey, rel]; Return[$Failed],
			  relno = relno[[1,1]]; relfn = rel],
	  _,
         Message[GetRelative::relkey, rel]; Return[$Failed]];
	relspace = Relatives[v][[relno]];
	If[relspace==None,
	  If[ $BatchInput || $BatchOutput,
	     Message[GetRelative::none, relfn, v]; Return[$Failed],
         relspace = Input[SPrint[GetRelative::prompt, relfn, v]];
		 If [!SymbolQ[relspace] || ProtectedQ[relspace],
		    Message[GetRelative::name]; Return[$Failed],
		    relfn[v->relspace]]]];
	relspace]

GetRelative::relkey = "Wrong relation ``"
GetRelative::none = "No relative `` is defined for ``"
GetRelative::name = "The name of the relative space should be a non-protrcted symbol" 
GetRelative::prompt = "Type the name for `` of ``: "


(*********************  MLeft  ******************)

MLeft[ m_->pm_, opt___Rule] :=
  ( Message[MLeft::self, m];
    m
  )

MLeft::self = "The MLeft relative of `1` is `1` itself"

MLeft[m_] := Relatives[m][[1]]


(*********************  MRight  ******************)

MRight[ m_->rm_, opts___Rule] :=
  ( If [(Clear /. {opts}) =!= False,
      Clear[rm];
      NewRelative[MRight, m->rm, opts]];
    rm/: Act[g_, v_rm] := ((-1)^(P[g])) ~SVTimes~ (Act[g, m @@ v] /. m -> rm);
    rm
  )

MRight[m_] := Relatives[m][[3]]


(*********************  PiLeft  ******************)

PiLeft[ m_->pm_, opts___Rule] :=
  ( If [(Clear /. {opts}) =!= False,
      Clear[pm];
      NewRelative[PiLeft, m->pm, opts]];
    pm/: Act[g_, v_pm] := ((-1)^(P[g])) ~SVTimes~ (Act[g, m @@ v] /. m -> pm);
    pm
  )

PiLeft[m_] := Relatives[m][[7]]


(*********************  PiRight  ******************)

PiRight[ m_->mp_, opts___Rule] :=
  ( If [(Clear /. {opts}) =!= False,
      Clear[mp];
      NewRelative[PiRight, m->mp, opts]];
    mp/: Act[g_, v_mp] := Act[g, m @@ v] /. m -> mp;
    mp
  )

PiRight[m_] := Relatives[m][[5]]


(**************** CoLeft (left even forms) ***********)

CoLeft[ m_->cm_, opts___Rule] :=
  Module[{i, j, k, pf, cf, pm, pfm, l, m1 },
  With[{g = Algebra /. {opts} /. Algebra->TheAlgebra[m]},
   If [(Clear /. {opts}) =!= False,
      Clear[cm];
      NewRelative[CoLeft, m->cm, opts]];
   If[g===None,
    cm::usage =	SPrint["`` is the space of the left even forms on ``", cm, m],
    pm = Table[0, {i, Dim[m]}, {j, Dim[g]}];
    For [i=1, i<=Dim[g], ++i, For[j=1, j<=Dim[m], ++j,
      pf = VNormal @ Act[g[i],m[j]];      
      If [pf==0, Continue[]];
      If [ Head[pf]=!=VPlus, pf = {pf}];
      For [l=1, l<=Length[pf], ++l,
        pfm = pf[[l]];
        {m1, cf} = SplitPtrn[m[_]] @ pfm;
        k = m1[[1]];
        pm[[k,i]] = VPlus[pm[[k,i]], 
			   (-(-1)^(P[g[i]]*P[m[k]])*cf) ~SVTimes~ cm[j] ];
      ]
    ]];
    ActTable[g, cm] ^= pm;
    Act[g[i_], cm[j_]] ^:= ActTable[g,cm][[j,i]];
    TheAlgebra[cm] ^= g;
    cm::usage =
	SPrint["`` is the ``-module of the left even forms on ``", cm, g, m]]
  ]]

CoLeft[m_] := Relatives[m][[2]]


(**************** CoRight (right even forms) ***********)

CoRight[ m_->mc_, opts___Rule] :=
  Module[{mr},
    mr = MRight[m];
    If[mr===None, mr=.; MRight[m->mr]];
	CoLeft[mr->mc, opts];
	mc
  ]

CoRight[m_] := Relatives[m][[4]]


(************** DLeft (left odd forms) *************)

DLeft::dp = "Wrong value of optional paremeter DivPowers->`` in DLeft"
(*DLeft::dp2 =*)

DLeft[ m_->dm_, opts___Rule] :=
 Module[ {brk, cobrk=None, indg, indm, argsg, argsm, argsr, cmg, cmm, cmr,
	 arg, arm, arr, ptg, ptm, ptr, cmno, sol, coa, res, ptbg,
	 k, cf, m1, si, sj, dp},
 With[{g = Algebra /. {opts} /. Algebra->TheAlgebra[m]},
  If [(Clear /. {opts}) =!= False,  
    Clear[dm];
    NewRelative[DLeft, m->dm, opts]];
If[g===None,
  dm::usage = SPrint["`` is the space of the left derivatives on ``", dm, m],
(*else*)
  Bracket[dm] ^= brk = Bracket[m];
  dp = DivPowers /. {opts};
  Switch[dp,
    DivPowers, dp = DivPowersQ[dm,wPower],
    False,     If[DivPowersQ[dm,wPower], UnDivPowers[dm->wPower]],
    Wedge|wedge|wPower|True, dp = True; If[!DivPowersQ[dm,wPower], DivPowers[dm->wPower]],
    _, Message[DLeft::dp, dp]; Return[$Failed]];

  If[m===g, cobrk = CoAct /. {opts}];
  Switch[ BracketMode[dm] ^= BracketMode[m],
  (*case*) Regular,
    Components[dm] ^= Components[m] /. m->dm;
    indg = 0; (indg = Max[indg, #[[2]]])& /@ Components[g];
    indm = 0; (indm = Max[indm, #[[2]]])& /@ Components[m];
    argsg = Table[Unique["i$i",{Temporary}], {indg}];
    argsm = Table[Unique["j$i",{Temporary}], {indm}];
    argsr = Table[Unique["k$i",{Temporary}], {indm}];
    Do [ cmg = Components[g][[ig]];
	 arg = Take[argsg, cmg[[2]]];
	 ptg = (*Pattern[#, Blank[]]& /@*) cmg[[1]] @@ arg;
	 Clear[sol, coa];
	 sol[_] = {};
	 coa[_] = {};
	 Do [ cmm = Components[m][[im]];
	      arm = Take[argsm, cmm[[2]]];
	      ptm = (*Pattern[#, Blank[]]& /@*) cmm[[1]] @@ arm;
	      res = brk[ptg,ptm] /. VSumOutRule[VIf];
	      If [Head[res]=!=VPlus, res = {res}];
	      Scan[( cmno = CompNo[#, Components[m]];
		cmr = Components[m][[ cmno ]];
		arr = Take[argsr, cmr[[2]]];
		sol[cmno] = {sol[cmno], CoIndex[#, arr, arm, cmm[[4]]]};
		If[cobrk=!=None, 		(* Define coaction on dg *)
		   coa[cmno] = {coa[cmno], (DerIndex[#, arr, arg, arm, 
				    cmm[[3]], cmm[[4]]]) /. SymmetricRule[wedge] }
		]
	      )&, res],
	    { im, Length[ Components[m] ] }
	 ];
	 Do [ cmr = Components[dm][[im]];
	      arr = Take[argsr, cmr[[2]]];
	      ptr = cmr[[1]] @@ arr;
	      ptrb = Pattern[#, Blank[]]& /@ ptr;
	      ptgb = Pattern[#, Blank[]]& /@ ptg;
	      res = ((-1)^(P[ptg]P[ptr])) ~ SVTimes~
			(VPlus @@ Flatten[sol[im]] /. m->dm);
	      If [FreeQ[res,VSum|Sum],
		dm /: brk[ ptgb, ptrb ] := Evaluate[res],
	      (*else*)
		UniqueCounters[ res //. JoinVSumRule /. VSumNormRule ];
		With[ { ind = ui$list, res = ui$res},			 
		     dm/: brk[ptgb, ptrb] := WithUnique[ind, res] ]
	      ];
	      If[cobrk=!=None, 
		  res = VPlus @@ Flatten[coa[im]] /. m->dm;
		  If [FreeQ[res,VSum|Sum],
			cobrk[ptrb] ^:= Evaluate[res],
		  (*else*)
		     UniqueCounters[ res //. JoinVSumRule /. VSumNormRule ];
		     With[ { ind = ui$list, res = ui$res},
			cobrk[ptrb] ^:= WithUnique[ind, res] ]
		  ]
	      ]
	    ,{ im, Length[ Components[m] ] }
	 ],
       { ig, Length[ Components[g] ] }
     ],
  (*case*) Tabular,
    sol = Table[0, {Dim[m]}, {Dim[g]}];
    Do [ res = VNormal @ Act[g[i],m[j]];  
	 If [res==0, Continue[]];
	 If [ Head[res]=!=VPlus, res = {res}];
	 Do [ ptm = res[[l]];
	      {m1, cf} = SplitPtrn[m[_]] @ ptm;
	      k = m1[[1]];
	      sol[[k,i]] = VPlus[sol[[k,i]], 
			  (-(-1)^(P[g[i]]*(P[m[k]]+1))*cf)~SVTimes~dm[j] ],
	    {l, Length[res]}
      ],
      {i, Dim[g]}, {j, Dim[m]}
    ];
    ActTable[g, dm] ^= sol;
    brk[g[i_], dm[j_]] ^:= ActTable[g,dm][[j,i]];
    If [cobrk=!=None,		(* define coaction  dg -> dg/\dg *)
	coa = Table[{}, {Dim[m]}];
	Do [ si = P[g[i]];
             Do [ sj = (-1)^(si*(1-P[g[j]]));
		  res = VNormal @
                    Which[i!=j, Act[g[i],g[j]],
                          si==0, 0,
                          $p==2, Squaring[g[i],Act],
                          True, (1/2) ~SVTimes~ Act[g[i],g[j]]];
		  If [res==0, Continue[]];
		  If [ Head[res]=!=VPlus, res = {res}];
		  Do [ {m1, cf} = SplitPtrn[m[_]] @ res[[l]];
			k = m1[[1]];
			AppendTo[coa[[k]],
			   Which[
                              i!=j, (sj*cf)~SVTimes~wedge[dm[i],dm[j]],
                              dp,   (sj*cf*2)~SVTimes~wPower[dm[i],2],
                              True, (sj*cf)~SVTimes~wPower[dm[i],2]]
			 ],
		     {l, Length[res]}
		  ],
	       {j, i, Dim[m]}
	     ],
	  {i, Dim[g]}
	];
	CoActList[dm] ^= Apply [VPlus, coa, {1}]; 
	cobrk[dm[i_]] ^:= CoActList[dm][[i]];
    ]
  ];
  TheAlgebra[dm] ^= g;
  dm::usage =
	SPrint["`` is the ``-module of the left derivatives on ``", dm, g, m]]
]]

DLeft[m_] := Relatives[m][[8]]

SetProperties[CoAct, {Vector, Vector->__, Linear->First} ]


(**************** DRight (right odd forms) ***********)

DRight[ m_->md_, opts___Rule] :=
  Module[{mp},
    mp = PiRight[m];
    If[mp===None, mp=.; PiRight[m->mp]];
	CoLeft[mp->md, opts];
	md
  ]

DRight[m_] := Relatives[m][[6]]


(* ===================== Regular components =================== *)

CompNo[elt_, cmplist_] :=
  Do [ cmp$$ = cmplist[[i]];
       If [ {Head[elt],Length[elt]} === Take[cmp$$,2],
	  Return[ If [Length[cmp$$]>=4 || cmp$$[[4]]@@elt, i, Null] ]],
     {i, Length[cmplist]}
  ]

CompNo[elt:(_VIf|_SVTimes), cmplist_] := CompNo[Last[elt], cmplist]
CompNo[elt_VSum, cmplist_] := CompNo[First[elt], cmplist]

SetProperties[{CoIndex, DerIndex}, {Vector, Vector->First, Additive->First}]

CoIndex[ VIf[cond_.,SVTimes[c_.,g_[ft__]]], {b__}, {x__}, if_:(True&) ] :=
    Module[{equ, uneq, neweq},
	equ = Which[ FreeQ[cond, Equal], True,
		     Head[cond]===Equal, cond,
		     Head[cond]===And, Cases[cond, _Equal],
		     True, Message[CoIndex::cond, cond]; False
	];
	equ = Flatten @ {equ, Thread[{ft}=={b}] };
	neweq = Eliminate[equ,{x}];
	If [ ListQ[neweq], neweq = And @@ neweq ];
	equ = equ /. Solve[neweq][[1]];
	VPlus @@ (VIf[neweq && if[x],
			Evaluate[SVTimes[-c,g[x]]]] /. Solve[equ, {x}])
  ]

Off1[msg__] := With[{ret=Select[Hold[msg],Head[#]=!=$Off]}, Off@@ret; ret]
On1[Hold[msg__]] := On[msg]

DerIndex[ VIf[cond_.,SVTimes[c_.,g_[ft__]]],
				{b__}, {x__}, {y__}, iter_, if_:(True&) ] :=
    Module[{equ, solu, ind, iterat, itvar, inviter, hmsg},
	equ = Which[ FreeQ[cond, Equal], True,
		     Head[cond]===Equal, cond,
		     Head[cond]===And, Cases[cond, _Equal],
		     True, Message[CoIndex::cond, cond]; False
	];
	equ = Flatten @ {equ, Thread[{ft}=={b}] };
        hmsg = Off1[Solve::svars];
	solu = Solve[equ, Reverse[{x,y}]][[1]];
	On1[hmsg];
	equ = equ /. solu;		(* the remaining conditions *)
	If [ ListQ[equ], equ = And @@ equ ];
	ind = Complement[{x,y}, First/@solu];	(* the remaining indeces *)
	If [ind=!={},			(* the result is the sum *)
	   iterat = iter[x];
	   itvar = First /@ iterat;
	   Do [ pos = Position[itvar, ind[[i]]] [[1,1]];
		Do [ inviter = InvertIter[iterat[[j]], iterat[[j+1]]];
		     iterat[[j]] = inviter[[1]];
		     iterat[[j+1]] = inviter[[2]],
		   {j, pos-1, i, -1}
		],
	      {i, Length[ind]}
	   ];
	   iterat = Take[iterat, Length[ind]];
	   VSum[ Evaluate[VIf[ equ && if[x],
		Evaluate @ SimplifySign @
			SVTimes[-(-1)^P[g[y]] c/2, wedge[g[y],g[x]]]]/.solu],
		Evaluate[Sequence @@ iterat]],
        (*else*)
	   VIf[equ&&if[x],
		Evaluate @ SimplifySign @
			SVTimes[-(-1)^P[g[y]]c/2, wedge[g[y],g[x]]] /. solu] 
	]
  ]

InvertIter::unlin = "Cannot find the limits of the sum"

InvertIter[{x_, fx_, tx_}, {y_, fy_, ty_}] :=
  With[{dfy = D[fy,x], dty = D[ty,x]},
    Module[{lx={fx}, rx={tx}, ly=fy, ry=ty, r},
	If [dfy!=0, r = Solve[fy==y, x][[1,1,2]];
	   If[dfy>0, AppendTo[rx, r]; ly = fy /. x->fx,
	   (*else*)  AppendTo[lx, r]; ly = fy /. x->tx ]
	];
	If [dty!=0, r = Solve[ty==y, x][[1,1,2]];
	   If[dty>0, Append[lx, r]; ry = ty /. x->tx,
	   (*else*)  Append[rx, r]; ry = ty /. x->fx ]
	];
       lx = Max @@ lx /. {Max[y,ly]->y, Max[ry,y|ly]->ry}; 
       rx = Min @@ rx /. {Min[y,ry]->y, Max[ly,y|ry]->ly}; 
       {{y, ly, ry}, {x, Max @@ lx, Min @@ rx}}
    ] /; NumberQ[dfy] && NumberQ[dty] || (Message[InvertIter::unlin]; False)
  ]


DPrint[1, "SuperLie`Space` loaded"]
End[]
EndPackage[]
