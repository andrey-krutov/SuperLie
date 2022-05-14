BeginPackage["SuperLie`Det`"];

(* Determinant of polynomial matrix *)



rowt::usage = "selected row"
colt::usage = "selected column"
mrest::usage = "the matrix"
mfact::usage = "the extracted factor"

ini::usage = "ini[m,p1,...] initialize the calgication of determinant with parameters p1,..."

tcol::usage = "tcol[i] assigns and prints selected column"

prcol::usage = "prcol prints the selected columns"
prdeg::usage = "prdeg prints the maximal polymomial degrees in the rows of the matrix"

$prfunc::usage = "The value of $prfunc is a function applied to matrix element when printing. Default in Identity."

(*
optm::usage = optz::usage = optd::usage =
 "optm, optz, and optd select optimal row/column for eliminating from matrix
(using optimization criteria)."

scol::usage = scoz::usage = scod::usage =
 "scol, scoz, and scod select optimal row/column for eliminating from matrix
(using optimization criteria) and print the contents of the selected column"
*)

optm::usage =
 "optm select optimal row/column for eliminating from matrix"

scol::usage = 
 "scol select optimal row/column for eliminating from matrix
and print the contents of the selected column"

adr::usage =
 "adr[i,j,c] adds c*row_j to row_i and prints the contents of the selected column.
adr[i,j] is equivalent to adr[i,j,1]. adr[{i1,j1[,c1]},...] adds multiple rows
and that prints the contents of the selected column."

fat::usage =
 "fat extracts all common factors from the rows of the matrix"

elim::usage =
 "elim[i,j] eliminate row_i and col_j from matrix"

sim::usage =
 "sim elimitates all row and column that have monomial elements" 

simt::usage =
 "simt elimitates the selected row and column than find and print new optimal selection" 

expn::usage =
 "expn expands the matrix elements"

sav::usage =
 "sav saves the current matrix to \"det.pnt\" in the current directory"

fini::usage =
 "fini calculate the determinant of the matrix (usung Standard Mathematica functions)
and save the result to \"det.sav\" in the current directory"

Begin["det`"]

ini[m_,par___] := (mfact = 1; mrest = m; vars[par];);

(* ------ Find optimal (i,j) for simplification of "mrest" ------ *)
optm := ( {rowt,colt} = optmm )
optmm :=
  Module [{i,j,l,r,i0,j0,n0=Infinity,d0=Infinity,n,s},
    l = Length[mrest];
    For [i=1, i<=l, ++i,
	r = mrest[[i]];
	For [j=1, j<=l, ++j,
	   s = r[[j]];
	   d = dg[s];
	   Switch [s,
	      0, Continue[],
	      1|(-1), Return[{i,j}],
	     _Integer, n = Abs[s],
             _Rational, Abs[Numerator[s]*Denominator[s]],
	     _Plus, n=Length[s],
	     _, n=If[d==1, 1, 10000000]
           ];
 	 If [d<d0 || (d==d0 && n<n0), d0 = d; n0 = n; i0=i; j0=j]
       ];
    ]; 
   Print[mrest[[i0,j0]]];
   {i0,j0}
  ]


optz := ( {rowt,colt} = optzm )
optzm :=
  Module [{nz,c,c0,i,j,l,r,i0,j0,n0=0,r0,d0=Infinity,n,s},
    l = Length[mrest];
    For [j=1, j<=l, ++j,
        c = #[[j]]& /@ mrest;
        nz = Count[c, 0];
        If[nz>n0, n0 = nz; c0 = c; j0 = j]];
    If[n0==0, Return[optmm]];
    r0 = n0;
    For [j=1, j<=l, ++j,
        c = mrest[[j]];
        nz = Count[c, 0];
        If[nz>r0, r0 = nz; c0 = c; j0 = j]];
    If[r0>n0, mrest=Transpose[mrest]];
    n0 = Infinity;
    For [i=1, i<=l, ++i,
	s = c0[[i]];
	d = dg[s];
	Switch [s,
	      0, Continue[],
	      1|(-1), Return[{i,j0}],
	     _Integer, n = Abs[s],
             _Rational, Abs[Numerator[s]*Denominator[s]],
	     _Plus, n=Length[s],
	     _, n=If[d==1, 1, 10000000]
        ];
 	If [d<d0 || (d==d0 && n<n0), d0 = d; n0 = n; i0=i]
    ];
   Print[c0[[i0]]];
   {i0,j0}
  ]

optd := ( {rowt,colt} = optzd )
optzd :=
  Module [{nz,c,c0,i,j,l,r,i0,j0,n0=Infinity,r0,d0=Infinity,n,s},
    l = Length[mrest];
    For [j=1, j<=l, ++j,
        c = #[[j]]& /@ mrest;
        nz = Deg[c];
        If[nz<n0, n0 = nz; c0 = c; j0 = j]];
    r0 = n0;
    For [j=1, j<=l, ++j,
        c = mrest[[j]];
        nz = Deg[c];
        If[nz<r0, r0 = nz; c0 = c; j0 = j]];
    If[r0<n0, mrest=Transpose[mrest]];
    n0 = Infinity;
    For [i=1, i<=l, ++i,
	s = c0[[i]];
	d = dg[s];
	Switch [s,
	      0, Continue[],
	      1|(-1), Return[{i,j0}],
	     _Integer, n = Abs[s],
             _Rational, Abs[Numerator[s]*Denominator[s]],
	     _Plus, n=Length[s],
	     _, n=If[d==1, 1, 10000000]
        ];
 	If [d<d0 || (d==d0 && n<n0), d0 = d; n0 = n; i0=i]
    ];
   Print[c0[[i0]]];
   {i0,j0}
  ]


(* ---------- Assign current column and print it --------- *)
tcol[i_] := (colt = i; prcol; )

(* ---------- Print current column ------------ *)

$prfunc = #&;
prcol := Do[Print[i," : ", $prfunc[mrest[[i,colt]]]],{i,Length[mrest]}]

dg[(List|Plus)[v__]] := dg /@ Unevaluated[Max[v]]
dg[Times[u_,v__]] := dg /@ Unevaluated[u+v]
vars[x__]:=
 (var = Alternatives[x];
  dg[var^n_.] := n
 )
dg[_] = 0
dg[0] = "-"
prdeg := (Print[dg /@ #]& /@ mrest;)

(* ------ Find, set current and print optimal row and column ------ *)
scol :=
  (  optm;
     Print ["col = ", colt, ",  row = ", rowt];
     prcol;
  )
scoz :=
  (  optz;
     Print ["col = ", colt, ",  row = ", rowt];
     prcol;
  )

scod :=
  (  optd;
     Print ["col = ", colt, ",  row = ", rowt];
     prcol;
  )

(* ----- Add rows (i) + c*(j), print current column ----- *)
adr$[i_,j_,c_:1] := 
  (mrest = ReplacePart[mrest, Expand[mrest[[i]] + c * mrest[[j]]], {i}])

adr[arg__List] := (Apply[adr$, {arg}, 1 ]; prcol)

adr[i_,j_,c_:1] := ( adr$[i,j,c];  prcol)

(* ------ Remove (i0)x(colt); find new (rowt)x(colt) ---------- *)
elim[i0_,j0_] :=
  Module [{i,j,l,r,n0=Infinity,d0=Infinity,s0,n,s, s1, s2, h, v, fact},
    l = Length[mrest];
    s0 = Factor[mrest[[i0,j0]]];
    fact = (-1)^(i0+j0)*s0;
    h = Drop[mrest[[i0]],{j0}];
    v = Factor /@ Drop[#[[j0]]& /@ mrest, {i0}];
    mrest = Drop[#,{j0}]& /@ Drop[mrest,{i0}];
    For [ i=1, i<l, ++i,
      If [ v[[i]]==0, Continue[] ];
      s = PolynomialGCD[s0, v[[i]]];
      s1 = Cancel[s0/s];
      s2 = Cancel[v[[i]]/s];
      mrest[[i]] = Expand /@ (s1*mrest[[i]] - s2*h);
      fact /= Factor[s1];
    ];
    mfact = Cancel[mfact*fact];
  ];

(* ------ Remove (i0)x(colt); find new (rowt)x(colt) ---------- *)
simt := (elim[rowt,colt]; scol;)


(* ------- Remove all monomial entries in the matrix --------- *)
 sim :=
   Module[{s},
     While[Length[mrest]>0, 
       fat;
       optm;
       s = mrest[[rowt,colt]];
       If [Head[s]===Plus, prcol; Return[]];
       Print["simpl : ", s];
       simt;
     ];
    Cancel[mfact]
  ];


(* ------- Extract common factor from {P1, P2, ...} ----------- *)
VFact[v_] :=
  Module [{i, l},
(*   If [!VectorQ[v], Print ["Not vector ", v]; Return [1] ]; *)
   (*Print["VFact[",v,"]"];*)
   l = Length[v];
   For[fact=Factor[v[[1]]]; i=2, fact=!=1 && i<=l, ++i, 
		(*Print ["GCD( ",fact, "   ,   ", v[[i]], " )"];*)
		fact = PolynomialGCD[fact, Factor[v[[i]]] ] ];
   frest = If [fact=!=1, Expand[Cancel[v/fact]], v ]
   (*Print ["      = ", fact, " * ", frest];*)
  ];

(* ------- Extract common factors from rows ----------- *)
fat :=
  Module [{i, l},
    l = Length[mrest];
    For [i=1, i<=l, ++i,
      Print["i=",i];
      VFact[mrest[[i]]];
      If [fact=!=1, mrest[[i]] = frest;  
		    mfact *= Factor[fact]; Print[fact] ];
    (*  VFact[#[[i]]& /@ mrest];
      If [fact=!=1, 
          mrest = MapIndexed[ ReplacePart[#1,frest[[#2[[1]] ]],i]&, mrest];
	  mfact *= Factor[fact]; Print[fact] ];*)
    ];
    Print ["nfact = ", mfact];
  ];

(* ------ Expand, transpose, save --------------- *)
expn := (mrest = Expand[mrest]; scol);		

tran := (mrest = Transpose[mrest]; {rowt,colt} = {colt,rowt};);

sav := Write["det.pnt", {mfact, mrest}];
savc := (Write["det.pnt", 
		"{mfact,mrest} = "//OutputForm,
		{mfact, mrest}, ";"//OutputForm];
	Close["det.pnt"];)

(* ----- Simplify (i)x(colt) using row(s) (j0) or {(j0),...} or All ---- *)
red[i_,j0_:All] :=
  Module[{j, jm, lj, ji, tmp$},
    jm = Switch [j0,
        All,  Range[Length[mrest]],
	_List, j0,
	_, {j0} ];
    jm = Select[jm, (#!=i && mrest[[#,colt]]=!=0)&];
    lj = Length[jm];
    For [ji=1, ji<=lj, ++ji,
      j = jm[[ji]];
      tmp$ = PolyQuot[ mrest[[i,colt]], mrest[[j,colt]], vars ];
      If [tmp$=!=0, mrest[[i]] = Expand[mrest[[i]] - tmp$ * mrest[[j]] ] ]
    ];
    If [lj>0, prcol];
  ]
  
red[i_,j_,k__] := red[i, {j,k}];

(* ------- Compute Det[mrest] and write the result ------------- *)
fini :=
 ( mfact = Cancel[mfact * Factor[Det[mrest]]];
   Write["det.sav", dsh, mfact];
   Close["det.sav"];
   mfact
 )

End[]
EndPackage[];