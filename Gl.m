(* --- gl.m ------- The definition of algebra gl(n|m) --------- *)

BeginPackage["SuperLie`Gl`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`", "SuperLie`Space`"}]

SuperLie`Gl`glAlgebra::usage =
  "glAlgebra[name, vect] - defines \"name\" as a matrix Lie 
(super)algebra on the space \"vect\"; glAlgebra[matr, Dim->dim] -
defines \"matr\" as Lie (super)algebra of dim*dim matrices (if
dim={d1,d2,..} - d1 odd components, d2 - even, d3 - odd, ...).";

SuperLie`Gl`slAlgebra::usage =
  "slAlgebra[name, vect] - defines \"name\" as a traceless matrix Lie 
(super)algebra on the space \"vect\"; slAlgebra[matr, Dim->dim] -
defines \"matr\" as Lie (super)algebra of traceless dim*dim matrices (if
dim={d1,d2,..} - d1 odd components, d2 - even, d3 - odd, ...).";

SuperLie`Gl`pslAlgebra::usage =
  "pslAlgebra[name, vect] - defines \"name\" as a traceless matrix Lie 
(super)algebra on the space \"vect\"; pslAlgebra[matr, Dim->dim] -
defines \"matr\" as Lie (super)algebra of traceless dim*dim matrices (if
dim={d1,d2,..} - d1 odd components, d2 - even, d3 - odd, ...)."

Begin["$`"]


glAlgebra[g_, vect_Symbol, opts___Rule ] :=
  Module [{v, prop, emode},
    prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace] ];
    With[ {dm=Dim[vect],brk = KeyValue[ prop, Bracket]},
      Define[g, {Vector, BasisPattern->(_g), TheSpace->vect}];
      SetProperties[g, prop ];
      TheAlgebra[g] ^= g;
      Dim[g] ^= dm^2;
      PDim[g] ^= {PDim[vect][[1]]^2 + PDim[vect][[2]]^2,
		2 PDim[vect][[1]] PDim[vect][[2]] };
      If [PDim[vect][[1]]===0 || PDim[vect][[2]]===0,  P[g[__]] ^= 0,
	(*else*) If [IntegerQ[dm] && IntegerQ[P[vect[1]]],
			PList[g] ^= Table[P[vect[i]], {i, dm}];
	   		P[g[i_,j_]] ^:= Mod[#[[i]]+#[[j]], 2]& @ PList[g],
	   (*else*) P[g[i_,j_]] ^:= Mod[P[vect[i]]+P[vect[j]], 2]
      ]];
      Grade[g[i_,j_]] ^:= j - i;
      Weight[g[i_,j_]] ^:= WeightMark[dm, i, -j];
      brk[ x:g[i_,j_], y:g[k_,l_] ] ^:=  VIf[j==k, g[i,l]] ~VPlus~
		VIf[i==l, Evaluate[(-(-1)^(P[x]*P[y]))] ~SVTimes~ g[k,j]];
      emode = KeyValue[prop, Enum];
      If[ emode =!= False,
	EnumSet[g,  { 0, 0, 1 } -> { 0 :> Table[g[i,i], {i, dm}] },
		{ 1, dm-1, 1 } -> { deg_ :> Table[ g[i,i+deg], {i, dm-deg}] },
		{-1,-dm+1,-1 } -> { deg_ :> Table[ g[i-deg,i], {i, dm+deg}] }
	]
      ];
      Do[
       With[{v = Relatives[vect][[r]]}, If[v=!=None,
	TheAlgebra[v] ^= g;
        Switch[ Mod[r, 4],
	   1,  brk[ g[i_,j_], v[k_] ] ^:= Evaluate[ VIf[j==k, v[i] ]],
	   2,  brk[ g[i_,j_], v[k_] ] ^:= 
	         Evaluate[VIf[k==i, (-(-1)^(P[g[i,j]]*P[v[k]]))~SVTimes~v[j] ]],
	   3,  brk[ g[i_,j_], v[k_] ] ^:= 
		  Evaluate[ VIf[j==k, (-(-1)^P[g[i,j]])~SVTimes~v[i]] ],
	   0,  brk[ g[i_,j_], v[k_] ] ^:=
	         Evaluate[VIf[k==i, (-(-1)^(P[g[i,j]]*P[v[j]]))~SVTimes~v[j] ]]
        ]]],
	{r, 1, 8}
      ];
      g/: Squaring[_g,brk] = 0;
      BracketMode[g] ^= Regular;
      Components[g] ^= { {g, 2, {{#1,1,dm},{#2,1,dm}}&, True&} };
      g/: Components[g, Grade->0] = { {g[#1,#1]&, 1, {{#1,1,dim}}&, True&} };
      g/: Components[g, Grade->d_/;d>0] :=
			{ {g[#1,d+#1]&, 1, {{#1,1,dm-d}}&, True&} };
      g/: Components[g, Grade->d_/;d<0] :=
			{ {g[-d+#1,#1]&, 1, {{#1,1,dm+d}}&, True&} };
      Relatives[g] ^=  {g, None, None, None, None, None, None, None}
    ];
    g::usage = SPrint["`` = gl(``)", g, FDim[vect] ]
  ]

 glAlgebra[ name_, opts___Rule ] :=
   Module [ {vect, covect},
      VectorSpace[vect, opts, CoLeft->covect];
      Relatives[vect] ^= {vect, None, None, None, None, None, None, None};
      glAlgebra[name, vect, opts]
   ]

(* ---- The definition of algebra sl(n|m) --------- *)


slAlgebra[g_, vect_Symbol, opts___Rule ] :=
  Module [{i, v, prop, brk, emode, attrVIf = Attributes[VIf]},
    glAlgebra[g, vect, opts];
    With[ {dm=Dim[vect], brk=Bracket[g]},
      Attributes[VIf] = {};
      Dim[g] ^= dm^2 - 1;
      PDim[g] ^= {PDim[g][[1]] - 1, PDim[g][[2]] };
      P[g[_]] ^= 0;
      Grade[g[_]] ^= 0;
      Weight[g[_]] ^= WeightMark[dm];
      brk[ x:g[i_,j_], y:g[k_,l_] ] ^:= Evaluate @
	VPlus [ VIf[j==k && i!=l, g[i,l]],
		VIf[i==l && j!=k, (-(-1)^(P[x]*P[y])) ~SVTimes~ g[k,j]],
		VIf[i==l && j==k, ((-1)^P[vect[i]]) ~SVTimes~
		      VSum[((-1)^P[vect[ii]]) ~SVTimes~ g[ii], {ii,i->j}]] ]; 
      brk[ g[_], g[_] ] ^= 0;
      brk[ g[i_], g[k_,l_] ] ^:= Evaluate @
	VPlus [ VIf[i==k, g[k,l]],
		VIf[i+1==k, (-(-1)^(P[vect[i]]+P[vect[i+1]]))~SVTimes~g[k,l]],
		VIf[i==l, (-1)~SVTimes~g[k,l]],
		VIf[i+1==l, ((-1)^(P[vect[i]]+P[vect[i+1]]))~SVTimes~g[k,l]] ];
      brk[ y:g[k_,l_], x:g[i_] ] ^:= (-1) ~SVTimes~ brk[x,y];
      If[ IntegerQ[Enum[g]],
	g/: Enum[g, 1] = { 0 :> Table[g[i], {i, dm-1}] }
      ];
      Do[
	v = Relatives[vect][[r]];
	If [v===None, Continue[] ];
        Switch[ Mod[r, 2],
	   1,	brk[ g[i_], v[k_] ] ^:= 
		  Evaluate[ VIf[i==k, v[k]] ~VPlus~
					VIf[i+1==k, (-1) ~SVTimes~ v[k]]], 
	   0,	brk[ g[i_], v[k_] ] ^:=
		   Evaluate[ VIf[i==k, (-1) ~SVTimes~ v[k]]
					~VPlus~ VIf[i+1==k, v[k]]]
	],
	{r, 1, 8}
      ];
      Attributes[VIf] = attrVIf;
      Components[g] ^= { {g, 2, {{#1,1,dm},{#2,1,dm}}&, (#1!=#2)&},
			 {g, 1, {{#1, 1, dm-1}}&, True&} };
      g/: Components[g, Grade->0] = Components[g][[2]]
    ];
    g::usage = SPrint["`` = sl(``)", g, FDim[vect] ]
  ]

 slAlgebra[ name_, opts___Rule ] :=
   Module [ {vect, covect},
      VectorSpace[vect, opts(*, CoLeft->covect*)];
      Relatives[vect] ^= {vect, None, None, None, None, None, None, None};
      slAlgebra[name, vect]
   ]

(* --- psl.m ---- The definition of algebra psl(m|m) --------- *)


pslAlgebra::dim = "Algebra psl(m|n) exists only for m=n."

pslPrj[g_, j_, m_, mr_, js_] :=
 VSum[((js-k)/m) ~SVTimes~ g[ mr[[k]] ], {k, js+1, j-1}] ~VPlus~
	VSum[((m+js-k)/m) ~SVTimes~ g[ mr[[k]] ], {k, j, m+js-1}]

pslAlgebra[g_, vect_Symbol, opts___Rule ] :=
  Module [{i, v, prop, emode, k, p, mr, sep, next},
    If [PDim[vect][[1]] != PDim[vect][[2]],
	Message[pslAlgebra::dim];
	Return[]
    ];
    prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace] ];
    With[ { dm=Dim[vect], m=PDim[vect][[1]], brk=KeyValue[prop,Bracket] },
      Define[g, {Vector, BasisPattern->(_g), TheSpace->vect}];
      SetProperties[g, prop ];
      Dim[g] ^= dm^2 - 2;
      PDim[g] ^= { 2 m^2 - 2, 2 m^2 };
      PList[g] ^= Table[P[vect[i]], {i, dm}];
      mr = sep = next = Table[0, {dm}];
      k = {0,0};
      Do[ p = PList[g][[j]];
	  i = k[[p+1]];
	  If [i>0, next[[ mr[[p*m+i]] ]] = j ];
	  sep[[j]] = (k[[p+1]] = ++i) + p*m;
	  mr[[p*m+i]] = j,
        {j, dm}
      ];
      mrList[g] ^= mr;
      sepList[g] ^= sep;
      nextList[g] ^= next;
      P[g[i_,j_]] ^:= Mod[#[[i]]+#[[j]], 2]& @ PList[g];
      P[g[_]] ^= 0;
      Grade[g[i_,j_]] ^:= j - i;
      Grade[g[_]] ^= 0;
      Weight[g[i_,j_]] ^:= MapAt[-1&, MapAt[1&, Table[0, {dm}], i], j];
      brk[ g[i_,j_], g[k_,l_] ] ^:= 0 /; i!=l && j!=k;
      brk[ g[i_,j_], g[j_,l_] ] ^:= g[i,l] /; i!=l;
      brk[ g[i_,j_], g[k_,i_] ] ^:= 
	  (-(-1)^(P[g[i,j]]*P[g[k,i]])) ~SVTimes~ g[k,j] /; j!=k;
      brk[ g[i_,j_], g[j_, i_] ] ^:=
	With[{sp=sepList[g], mr=mrList[g], pl=PList[g]},
	   VSum[g[ mr[[k]] ], {k, sp[[i]], sp[[j]]-1}]
	   /; i<j && pl[[i]]==pl[[j]]
	];
      brk[ g[i_,j_], g[j_, i_] ] ^:=
	With[{sp=sepList[g], mr=mrList[g], pl=PList[g]},
	   VSum[(-1) ~SVTimes~ g[ mr[[k]] ], {k, sp[[j]], sp[[i]]-1}]
	   /; i>j && pl[[i]]==pl[[j]]
	];
      brk[ g[i_,j_], g[j_, i_] ] ^:=
	With[{sp=sepList[g], mr=mrList[g], pl=PList[g]},
		pslPrj[ g, sp[[i]], m, mr, m*pl[[i]] ] ~VPlus~
		pslPrj[ g, sp[[j]], m, mr, m*pl[[j]] ]
	  /; pl[[i]]!=pl[[j]]
	];
      brk[ g[_], g[_] ] ^= 0;
      brk[ g[i_], g[k__] ] ^:=
	(#[[i]] - #[[ nextList[g][[i]] ]])& [Weight[g[k]]]~SVTimes~g[k];
      brk[ g[k__], g[i_] ] ^:= 
	(- #[[i]] + #[[ nextList[g][[i]] ]])& [Weight[g[k]]]~SVTimes~g[k];
      g/: Squaring[_g,brk] = 0;
      emode = KeyValue[prop, Enum];
      If[ emode =!= False,
	EnumSet[g, 
	  { 0, 0, 1 } -> { 0 -> Delete[Table[g[i],{i,dm}],
				List /@ mrList[g][[{m, dm}]]] },
	  { 1, dm-1, 1 } -> { deg_ :> Table[ g[i,i+deg], {i, dm-deg}] },
	  {-1,-dm+1,-1 } -> { deg_ :> Table[ g[i-deg,i], {i, dm+deg}] }
	]
      ];
    g::usage = SPrint["`` = psl(``|``)", g, PDim[vect][[1]], PDim[vect][[2]] ]
  ]
 ]

 pslAlgebra[ name_, opts___Rule ] :=
   Module [ {vect, covect},
      VectorSpace[vect, opts, CoLeft->covect];
      pslAlgebra[name, vect]
   ]

End[]
EndPackage[]


