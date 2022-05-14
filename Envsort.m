(* --- Envsort.m ---- *)
(* The sorting rules for the product in enveloping algebras --- *)

BeginPackage["SuperLie`Envsort`", {"SuperLie`", "SuperLie`Domain`", "SuperLie`Space`"}]


(* === The product in the enveloping algebra === *)

EnvNormal::usage = "EnvNormal[e] gives the standard form of element e of an
enveloping algebra. EnvNormal[e,p] uses the function p[t1,t2] to determine
the required order in the product."

EnvSortRule::usage = "e //. EnvSortRule sorts the terms of the miltiplication
in enveloping algebra into canonical order."

$EnvLess::usage = "The value of $EnvLess is the default sorting function
for the product in enveloping algebras"


EnvelopingOperation::usage = "EnvelopingOperation[times,power,act,order]
defines times to be an operation in enveloping algebra with action act;
power is the power operation corresponding to times; order[f,g] is True if
times[f,g] is in the canonical order in the enveloping algebra."

EnvelopingSymbol::usage = "EnvelopingSymbol[symb,mult,brk,order]
introduces notations: symb[...] for the elements of basis of an enveloping
algebra, mult[...] for the multiplication in enveloping algebras with
bracket brk. The function order[f,g] should return True if symb[f,g] is
in the canonical order in the enveloping algebra."

ExpandOp::usage = "ExpandOp[expr,op] expands the operation in the expression
as (noncommutative) multiplication"

ExpandOpRule::usage = "expr //. ExpandOpRule[op] expands the operation in the 
expression as (noncommutative) multiplication"

(* === The composition of differential operators === *)

dSymbol::usage = "dSymbol[d] assigns the symbol used as differential
 operator: d[x]^n will represent the differential operator d/(dx)^n"

CleardSymbol::usage = "CleardSymbol[] clears the symbol that was used as
 differential operator"

dSortRule::usage = "expr //. dSortRule[d] sorts the terms in the composition
 of differential operators: d[x]x -> x d[x] + 1"

dNormal::usage = "dNormal[expr] gives the standard form of the composition
 of differential operators"

DiffAlgebra::usage = "DiffAlgebra[g,space] defines g as the algebra of
 differential operators on the given space."

Dc::usage = "Dc is the default name for the bracket in DiffAlgebra" 

Options[DiffAlgebra]={Bracket->Dc, D->d}

Begin["$`"] (* =============  Private section ============== *)

(* === The normal form of expressions in the enveloping aldebra === *)

envAtomQ[v_] := !MemberQ[{VTimes,VPower,VPlus,SVTimes}, Head[v]];

$EnvLess = (OrderedQ[{#1,#2}]&)

EnvSortRule:=
 { VPower[x_?envAtomQ /;P[x]==1, n_/;n>1] :>
	SVTimes[1/2, VTimes[Act[x,x], VPower[x,n-2]]],
   VTimes[a___, y_?envAtomQ,x_?envAtomQ, b___] /; !$EnvLess[y,x] :>
	VPlus[VExpand[VTimes[a,Act[y,x],b]],
	      SVTimes[ (-1)^(P[x]*P[y]), VTimes[a,x,y,b] ]],
   VTimes[a___, VPower[y_?envAtomQ,m_.]/;m>0,
		VPower[x_?envAtomQ,n_.]/;n>0, b___] /; !$EnvLess[y,x]:>
	VPlus[VExpand[VTimes[a,VPower[y,m-1],Act[y,x],VPower[x,n-1],b]],
	      SVTimes[ (-1)^(P[x]*P[y]),
		 VTimes[a,VPower[y,m-1],x,y,VPower[x,n-1],b] ]]
 };

EnvNormal[expr_] :=
   VNormal[expr //. VExpandRule //. EnvSortRule]

EnvNormal[expr_, p_] :=
  Block[{$EnvLess=p}, EnvNormal[expr]]

(* === Enveloping algebra with different operation === *)

envAtomQ[v_, op__] := !MemberQ[{VPlus,SVTimes,op}, Head[v]]

ExpandOp[expr_, op_] := expr //. ExpandOpRule[op]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 ExpandOpRule[op_] :=
  With[{pw = PowerOp[op]},
   If[pw===None,
    { wrapper[op[x___,y_VPlus, z___]] :> (op[x, #, z]& /@ y),
      wrapper[SVTimes[x_, y_VPlus]] :> (SVTimes[x, # ]& /@ y)
    },
    { wrapper[op[x___,y_VPlus, z___]] :> (op[x, #, z]& /@ y),
      wrapper[SVTimes[x_, y_VPlus]] :> (SVTimes[x, # ]& /@ y),
      wrapper[pw[SVTimes[c_,v_], n_]] :> (c^n) ~SVTimes~ pw[v,n],
      wrapper[pw[x_op, n_/;n>1]] :> op @@ Table[Sequence@@x, {n}],
      wrapper[pw[x_VPlus,n_Integer]] :> (op[pw[x,n-1],#]& /@ x) /; n>1
    }
   ]
  ]
]

EnvelopingOperation[times_, power_, brk_:Act, order_:$EnvLess] :=
( Attributes[times] = {};
  times[x_] := Unevaluated[x];
  SetAttributes[times, {Flat,OneIdentity}];
  SetProperties[times, {Vector,Vector->_,Linear}];
  PowerOp[times->power];
  power[x_/;(envAtomQ[x,times,power] && P[x]==1), n_/;n>1] :=
	 SVTimes[1/2, times[brk[x,x], power[x,n-2]]];
  power[SVTimes[c_, v_], k_] := SVTimes[c^k, power[v, k]];
  times[a___, y_/;envAtomQ[y,times,power], x_/;envAtomQ[x,times,power], b___] /; !order[y,x] :=
	VPlus[ExpandOp[times[a,brk[y,x],b],times],
	      SVTimes[ (-1)^(P[x]*P[y]), times[a,x,y,b] ]];
  times[a___, power[y_/;envAtomQ[y,times,power],m_.]/;m>0,
		power[x_/;envAtomQ[x,times,power],n_.]/;n>0, b___] /; !order[y,x] :=
   	  VPlus[ExpandOp[times[a,power[y,m-1],brk[y,x],power[x,n-1],b],times],
	      SVTimes[ (-1)^(P[x]*P[y]),
		 times[a,power[y,m-1],x,y,power[x,n-1],b] ]]
 );

EnvelopingOperation[times_, None, brk_:Act, order_:$EnvLess] :=
( Attributes[times] = {};
  times[x_] := Unevaluated[x];
  SetAttributes[times, {Flat,OneIdentity}];
  SetProperties[times, {Vector,Vector->_,Linear}];
  times[a___, x_/;(envAtomQ[x,times] && P[x]==1), x_, b___] :=
	SVTimes[1/2, times[a, brk[x,x], b]];
  times[a___, y_/;envAtomQ[y,times], x_/;envAtomQ[x,times], b___] /; !order[y,x] :=
	VPlus[ExpandOp[times[a,brk[y,x],b],times],
	      SVTimes[ (-1)^(P[x]*P[y]), times[a,x,y,b] ]]
 );



EnvelopingSymbol[symb_, op_, brk_:Act, order_:$EnvLess, vacuum_:(False&)] :=
( SetProperties[op, {Vector,Vector->_,Linear}];
  SetProperties[symb, {Vector,Vector->_,Graded}];
  P[symb] ^= 0;
  op[] = symb[];
  op[f_] := symb[f];
  op[symb[], f_symb] := f;
  op[f_symb, symb[]] := f;
  op[symb[], f_] := symb[f];
  op[f_, symb[]] := symb[f];
  op[symb[f___,g_], h_symb] := op[symb[f],op[g,h]];
  op[f_, symb[g_,h___]] :=
    If[order[f,g],
      If[f===g && P[f]===1,
        SVTimes[1/2, op[brk[f,g], symb[h]]],
      (*else*)
        symb[f,g,h]],
	(*else*) VPlus[op[brk[f,g],symb[h]],
                       VIf[!vacuum[symb[f,h]],SVTimes[(-1)^(P[f]P[g]), op[g,op[f,symb[h]]]]]]];
  op[f_,g_] := op[f,symb[g]];
  op[f__,g_,h_] := op[f,op[g,h]];
  LeibnizExpandFn[symb] ^= LeibnizExpandSymbol[op];
  Jacobi[brk->symb];
)

LeibnizExpandSymbol[op_][ f_[prm___,expr_], par_ ] := 
  Module [{ m, fm, s=1, s1, ph=P[Head[expr]] },
    If[!NumberQ[ph],
      Message[Leibniz::par, Head[expr]];
      ph = 0];
    VPlus @@ Table[
      m = expr[[i]];
      s1 = s;
      s *= (-1)^(par~Times~(P[m]+ph));
      If [(fm = f[prm,m])===0, 0,
	 (*else*) s1 ~SVTimes~ op[Take[expr,i-1],fm, Drop[expr,i]]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]

LeibnizExpandSymbol[op_][ f_[prm___,expr_], 0 ] := 
  Module [{ m, fm },
    VPlus @@ Table[
      m = expr[[i]];
      If [(fm = f[prm,m])===0, 0,
	 (*else*) op[Take[expr,i-1],fm, Drop[expr,i]]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]

(* === The normal form  of composition of differential operators === *)

dSymbol[d_] :=
( CleardSymbol[];
  Define[d, {Vector,Vector->_,Linear}];
  P[d[h_]] ^:= P[h];
  $d = d
)

dSymbol[] :=
 If[ValueQ[$d], $d, Message[dSymbol::missing];]

dSymbol::missing = "The symbol for differential operator is not assigned.
 Enter dSymbol[d] to assign it"

CleardSymbol[] :=
 If [ValueQ[$d],
   With[{d=$d}, Clear[d]];
   $d=.]
 

nondQ[e_] := !MemberQ[{$d,VPlus,VTimes,SVTimes}, Head[e]];
nondQ[VPower[e_, _]] := nondQ[e];

diffV[u_, v_] :=  
    Head[u] =!= Head[v] || Length[u] != Length[v] || 
      Do[If[u[[i]] != v[[i]], Return[True]],
	 {i, 1, Length[v]}]

diffV[u_?AtomQ,v_] := u=!=v;
dSortRule :=
With[{d=$d},
{VTimes[x___, VPower[d[v_], p_.], VPower[v_, n_.], y___] :>
   VSum[SVTimes[Binomial[p, i]Pochhammer[n-i+1,i],
                VTimes[x, VPower[v, n-i], VPower[d[v], p-i], y]],
	 {i, 0, Min[p, n]}] /; P[v] == 0, 
 VTimes[x___, d[v_], v_, y___] :>
   VPlus[VTimes[x, y], SVTimes[-1, VTimes[x, v, d[v], y]]] /; P[v] == 1, 
 VTimes[x___, d[u_], v_?nondQ, y___] :> 
   SVTimes[(-1)^(P[u]P[v]), VTimes[x, v, d[u], y]] /; diffV[u, v], 
 VTimes[x___, z:VPower[d[u_], _.], w:VPower[v_?nondQ, _.], y___] :>
   VTimes[x, w, z, y] /; diffV[u, v] && (P[u] == 0 || P[v] == 0),
 VTimes[x:(___?nondQ), y:VPower[d[_], _.]...] :> 
   VTimes[VTimes[x] /. SymmetricRule[VTimes], 
          VTimes[y] /. SymmetricRule[VTimes]],
 VPower[x_?nondQ, d_] :> 0 /; P[x]==1 && (d>1 || d<-1), 
 VPower[d[x_], d_] :> 0 /; P[x]==1 && (d>1 || d<-1)
}]

dNormal[e_] := VNormal[e //. VExpandRule //. dSortRule]


(* ==== DiffAlgebra ==== *)

DiffAlgebra[g_,space_,opts___]:=
  With[{brk=Bracket/.{opts}/.Options[DiffAlgebra]/.Bracket->Dc,
        ds=D/.{opts}/.Options[DiffAlgebra]/.D->d,
		u=BasisPattern[space]},
   Vector[g];
   dSymbol[ds];
   BasisPattern[g] ^= Flatten[_VTimes|_VPower|u|ds[u]];
   Bracket[g] ^= brk;
   P[brk] ^= 0;
   brk[x_,y_] := dNormal[VPlus[VTimes[x,y],((-1)^(1+P[x]P[y]))~SVTimes~VTimes[y,x]]];
   g::usage = SPrint["`` is the algebra of differential opertors on ``",
     g, space]]

End[]
EndPackage[]
