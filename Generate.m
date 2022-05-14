BeginPackage["SuperLie`Generate`", {"SuperLie`", "SuperLie`Domain`"}]

GenBasis::usage =
 "GenBasis[g] is the representation of the basis of \"g\" in terms of
(free) generators.";

GenRel::usage = 
 "GenRel[g] is the list of relations between the generators of \"g\"."

ToDegree::usage =
 "ToDegree->n is an optional parameter for space constructors. It restricts the
calculations to the elements of polynomial degree d in terms of generators.
ToDegree[m] returns this limit. The results of operations in m are evaluated
only if its degree <= ToDegree[m]."

ToDegree::usage =
 "Option ToDegree->d restrict the calculation in algebra constructors to the
elements of polynomial degree d in terms of generators."


GRange::usage = "Replaced by ToDegree."

GRange = ToDegree;

(*JacRel::usage =
 "JacRel[g] is the list of Jacobi relations between the generators of \"g\"."*)

Begin["$`"]

NewValue[GenBasis, GenRel, ToDegree]

(* ----------- Step of generation ----------------------------------------- *)
(* 960630: new posibitity: restriction for Grade[g[i]] *)

StepGeneration[g_, deg_, rng_, Brk_, brk_, sqr_:False] :=
  Module[{ q, s, t, vars, jac, sol, solj={}, prevtmp, hl, i, j, k, l, mgr},
(* extend the table of commutators *)
      Clear[gen$var];
      VectorQ[gen$var]^=True;
      If [deg==1, Return[0]];
      With[{imin=gen$ind[[deg-1]], imax=gen$ind[[deg]]-1,
        jmax=If [2*(deg-1)<=rng, i, gen$ind[[rng-deg+2]]-1]},
        gen$tbl = Join[gen$tbl, Table[None, {i, imin, imax }, {j, jmax} ]];
        If[sqr, gen$sqr = Join[gen$sqr, Table[None, {i, imin, imax }]]]
      ];
(* the list "gt" of pairs [g[j],g[i]] of degree "r" *)
      gen$lst = prevtmp = gen$flag = {};
      For [q=1; l=0, q<=deg/2, ++q,
	s = deg-q;
	For [i=gen$ind[[q]], i<gen$ind[[q+1]], ++i,
	  If[NumberQ[maxGrade$], mgr = maxGrade$-Grade[g[i]]];
	  For [j=If[q==s, i, gen$ind[[s]]], j<gen$ind[[s+1]], ++j,
	    If [i==j && P[g[i]]==0, gen$tbl[[i,i]] = 0; Continue[] ];
	    If [NumberQ[maxGrade$] && (Grade[g[j]]>mgr), Continue[] ];
	    prevtmp = {prevtmp, i};		(* precedence for Holl basis *)
       If [sqr && i==j,
         gen$lst =  { gen$lst, Squaring[g[i],brk] };  (* name list *)
         hl = 1;
         gen$sqr[[i]] = gen$var[hl, ++l];
         gen$tbl[[j,i]] = SVTimes[2, gen$var[hl, l]],
       (*else*)
         gen$lst =  { gen$lst, brk[g[i],g[j]] };  (* name list *)
         hl = If[i>=gen$prev[[j]], 2, 0];
         gen$tbl[[j,i]] = gen$var[hl, ++l]
       ];
	    gen$flag = {gen$flag, hl};
      ] ] ];
    DPrint[4, "Added ", l, " pair(s)"];
    DPrint[5, "Added ", Flatten[gen$lst]];
      If [l==0, Return[0]];			(* No more elements *)
      gen$lst = Flatten[gen$lst];
      gen$flag = Flatten[gen$flag];
      prevtmp = Flatten[prevtmp];
(* Equations from Jacobi identities *)
      For [q=1, q<=deg/3, ++q,
        For[s=q, s<=(deg-q)/2, ++s,
          t = deg-q-s;
          Do [jac = VNormal[ VPlus[ Brk[g[i],Brk[g[j],g[k]]],
                               (-1) ~SVTimes~ Brk[ Brk[g[i],g[j]], g[k] ],
                               (-(-1)^(P[g[i]]*P[g[j]]))~SVTimes~Brk[g[j],Brk[g[i],g[k]]] ] /.
                        solj ];
	      vars = MatchList[jac, _gen$var];
	      If [vars=={}, Continue[] ];
   DPrint[5, "Solving ",   jac==0,  " # ", {i,j,k}->{g[i],g[j],g[k]}];
	      sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
	(*      sol = VSolve[jac==0, {vars[[1]]}] [[1]]; *)
   DPrint[5, "Solution ",   sol  ];
	      If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
                sol = MapAt[VNormal, sol[[1]], 2 ];
                solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
	      ],
              {i, gen$ind[[q]], gen$ind[[q+1]]-1},
              {j, Max[i,gen$ind[[s]]], gen$ind[[s+1]]-1},
              {k, Max[j,gen$ind[[t]]], gen$ind[[t+1]]-1}
          ]
      ] ];
(* Extra Jacobi identies for char=2 *)
      If[sqr && $p==2,
        For[s=1, s<=(deg-1)/2, ++s,
          q = deg-2*s;
          Do [ If[P[g[j]]==1,
                 jac = VNormal[
                    VPlus[
                      Brk[g[i],Squaring[g[j],Brk]],
                      (-1) ~SVTimes~ Brk[g[j], Brk[g[j], g[i]]]
                    ] /. solj ];
	         vars = MatchList[jac, _gen$var];
	         If [vars=={}, Continue[] ];
   DPrint[5, "Solving (sqr)",   jac==0, {i,j}->{g[i],g[j]} ];
	         sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
	(*      sol = VSolve[jac==0, {vars[[1]]}] [[1]]; *)
   DPrint[5, "Solution ",   sol  ];
	         If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
                   sol = MapAt[VNormal, sol[[1]], 2 ];
                   solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
	       ]],
	       {i, gen$ind[[q]], gen$ind[[q+1]]-1},
	       {j, Max[i,gen$ind[[s]]], gen$ind[[s+1]]-1}
	  ]
      ] ];

(* Extra Jacobi identies for char=3 *)
      If[$p==3 && Mod[deg,3]==0,
        q = deg/3;
        Do [ If[P[g[i]]==1,
              jac = VNormal[Brk[g[i],If[sqr, Squaring[g[i],Brk], Brk[g[i],g[i]]]] /. solj ];
              vars = MatchList[jac, _gen$var];
              If [vars=={}, Continue[] ];
   DPrint[5, "Solving (cub)",   jac==0, {i}->{g[i]} ];
              sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
      (*      sol = VSolve[jac==0, {vars[[1]]}] [[1]]; *)
   DPrint[5, "Solution ",   sol  ];
              If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
                sol = MapAt[VNormal, sol[[1]], 2 ];
                solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
             ]],
             {i, gen$ind[[q]], gen$ind[[q+1]]-1}
        ]
      ];

     (* gen$tbl = gen$tbl //. solj; *)
      Apply[Set, solj, {1}];
      gen$tbl = gen$tbl;
      If[sqr, gen$sqr = gen$sqr];
      DPrint[1, "npairs =  ",l,"  (",N[TimeUsed[ ]-$tm,4], " sec)"]; $tm = TimeUsed[];
      Return[l]
  ]


(* version with generators with different gradings *)

StepGenerationVG[g_, grade_, deg_, rng_, Brk_, brk_, sqr_:False] :=
  Module[{ q, s, t, vars, jac, sol, solj={}, prevtmp, hl, i, j, k, l, mgr, g1, g2, g3},
(* extend the tables of commutators and squares*)
      Clear[gen$var];
      VectorQ[gen$var]^=True;
      If [deg==1, Return[0]];
(* the list "gt" of pairs [g[j],g[i]] of degree "deg" *)
      gen$lst = prevtmp = gen$flag = {};
      For[g1=gr$min; l=0, g1<=Min[grade/2,grade-gr$min], g1++,
        g2 = grade - g1;
	(*If[grade>=2, DPrint[1,"Trying grades g1=",g1,", g2=",g2]];*)
        For [q=Max[1,deg-gen$rng[g2]], q<=Min[gen$rng[g1], If[g1==g2, deg/2, deg-1]], ++q,
	  s = deg-q;
	  (*If[grade>=2, DPrint[1,"Trying degrees d1=",q,", d2=",s]];*)
	  For [i=gen$ind[g1][[q]], i<gen$ind[g1][[q+1]], ++i,
	    For [j=If[g1==g2 && q==s, i, gen$ind[g2][[s]]], j<gen$ind[g2][[s+1]], ++j,
	      If [i==j && P[g[i]]==0, gen$tbl[[i,i]] = 0; Continue[] ];
	      prevtmp = {prevtmp, i};		(* precedence for Holl basis *)
	      If[j>Length[gen$tbl],  (* extend the tables if required *)
	        gen$tbl = Join[gen$tbl, Table[None, {ii, Length[gen$tbl]+1, j+25}, {ii}]];
                If[sqr, gen$sqr = Join[gen$sqr, Table[None, {ii, Length[gen$sqr]+1, j+25}]]]];
              If [sqr && i==j,
	        gen$lst =  { gen$lst, Squaring[g[i],brk] };	(* name list *)
                hl = 1;
                gen$sqr[[i]] = gen$var[hl, ++l];
                gen$tbl[[j,i]] = SVTimes[2, gen$var[hl, l]],
              (*else*)
	        gen$lst =  { gen$lst, brk[g[i],g[j]] };	(* name list *)
	        hl = If[i>=gen$prev[[j]], 2, 0];
	        gen$tbl[[j,i]] = gen$var[hl, ++l]];
	      gen$flag = {gen$flag, hl};
      ] ] ] ];
    DPrint[4, "Added ", l, " pair(s)"];
      If [l==0, Return[0]];			(* No more elements *)
      gen$lst = Flatten[gen$lst];
      gen$flag = Flatten[gen$flag];
      prevtmp = Flatten[prevtmp];
(* Equations from Jacobi identities *)
      For[g1=gr$min, g1<=Min[grade/3,grade-2*gr$min], g1++,
       For[g2=g1, g2<=Min[(grade-g1)/2,grade-g1-gr$min], g2++,
        g3 = grade-g1-g2;
        For [q=1, q<=Min[gen$rng[g1],Which[g1==g3, deg/3, g1==g2, (deg-1)/2, True, deg-2]], ++q,
	 For[s=q, s<=Min[gen$rng[g2],If[g2==g3, (deg-q)/2, deg-q-1]], ++s,
	  t = deg-q-s;
	  If[t<=gen$rng[g3],
	   Do [jac = VNormal[ VPlus[ Brk[g[i],Brk[g[j],g[k]]],
		(-1) ~SVTimes~ Brk[ Brk[g[i],g[j]], g[k] ],
		(-(-1)^(P[g[i]]*P[g[j]]))~SVTimes~Brk[g[j],Brk[g[i],g[k]]] ] /.
		 solj ];
	      vars = MatchList[jac, _gen$var];
	      If [vars=={}, Continue[] ];
   DPrint[5, "Solving ",   jac==0  ];
	      sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
   DPrint[5, "Solution ",   sol  ];
	      If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
			sol = MapAt[VNormal, sol[[1]], 2 ];
			solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
	      ],
	    {i, gen$ind[g1][[q]], gen$ind[g1][[q+1]]-1}, 
	    {j, Max[i,gen$ind[g2][[s]]], gen$ind[g2][[s+1]]-1},
	    {k, Max[j,gen$ind[g3][[t]]], gen$ind[g3][[t+1]]-1}
	  ]]
      ]]]];
(* Extra Jacobi identies for char=2 *)
      If[sqr && $p==2,
       For[g2=gr$min, g2<=(grade-gr$min)/2, g2++,
        g1 = grade-2*g2;
        For [s=1, s<=Min[gen$rng[g2],(deg-1)/2], ++s,
	 For[s=q, s<=Min[gen$rng[g2],If[g2==g3, (deg-q)/2, deg-q-1]], ++s,
	  q = deg-2*s;
	  If[q<=gen$rng[g1],
	   Do [ If[P[g[j]]==1,
              jac = VNormal[
                    VPlus[
                      Brk[g[i],Squaring[g[j],Brk]],
		      (-1) ~SVTimes~ Brk[g[j], Brk[g[j], g[i]]]
                    ] /. solj ];
	      vars = MatchList[jac, _gen$var];
	      If [vars=={}, Continue[] ];
   DPrint[5, "Solving ",   jac==0  ];
	      sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
   DPrint[5, "Solution ",   sol  ];
	      If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
			sol = MapAt[VNormal, sol[[1]], 2 ];
			solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
	      ]],
	    {i, gen$ind[g1][[q]], gen$ind[g1][[q+1]]-1},
	    {j, Max[i,gen$ind[g2][[s]]], gen$ind[g2][[s+1]]-1}
	  ]]
      ]]]];
(* Extra Jacobi identies for char=3 *)
      If[$p==3 && Mod[deg,3]==0,
        q = deg/3;
        Do [ If[P[g[i]]==1,
              jac = VNormal[Brk[g[i],If[sqr, Squaring[g[i],Brk], Brk[g[i],g[i]]]] /. solj ];
              vars = MatchList[jac, _gen$var];
              If [vars=={}, Continue[] ];
   DPrint[5, "Solving (cub)",   jac==0, {i}->{g[i]} ];
              sol = VSolve[jac==0, {vars[[1]]}, InverseFunctions->True, VerifySolutions->False] [[1]];
      (*      sol = VSolve[jac==0, {vars[[1]]}] [[1]]; *)
   DPrint[5, "Solution ",   sol  ];
              If [sol=!={}, gen$flag[[ sol[[1,1,-1]] ]] = True;
                sol = MapAt[VNormal, sol[[1]], 2 ];
                solj = Append[ MapAt[VNormal,#/.sol,2]& /@ solj, sol];
             ]],
             {i, gen$ind[[q]], gen$ind[[q+1]]-1}
        ]
      ];
     (* gen$tbl = gen$tbl //. solj; *)
      Apply[Set, solj, {1}];
      gen$tbl = gen$tbl;
      If[sqr, gen$sqr = gen$sqr];
      DPrint[1, "npairs =  ",l,"  (",N[TimeUsed[ ]-$tm,4], " sec)"]; $tm = TimeUsed[];
      Return[l]
  ]



(* --------- Extension of the the basis --------------- *)

StepExtendBasis[g_, npairs_,sqr_:False] :=
  Module [{ i, rdim, dim, rng, par={} },
      rng = Length[gen$ind];
      dim = gen$ind[[-1]]-1;
      For [ i=1, i<=npairs, ++i,		(* add gen$var[i] to basis *)
	If [ gen$flag[[i]], Continue[] ];	(* gen$var[i] was removed *)
	gen$basis = {gen$basis, gen$lst[[i]]};
	If [gen$super, par = {par, P[ gen$lst[[i]] ]} ];
	gen$prev = {gen$prev, gen$lst[[i,1,1]]};
	gen$var[_,i] = g[++dim]
      ];

      gen$tbl = gen$tbl//.RestoreSV;		(* replace all gen$var[i] *)
      If[sqr, gen$sqr = gen$sqr//.RestoreSV];
      gen$rel = gen$rel//.RestoreSV;
      Clear[gen$var];
      VectorQ[gen$var]^=True; 
      AppendTo[gen$ind, dim+1];
      rdim = gen$ind[[-1]] - gen$ind[[-2]];
      If [rdim>0,
	gen$rng = rng;
	gen$deg = Join[gen$deg, Table[rng, {rdim}]]; 
        gen$prev = Flatten[gen$prev];
      ];
      If [gen$super,
	gen$par = Join[gen$par, Flatten[par]];
        i = Plus @@ gen$par;
        DPrint[1, "r = ", rng,  ", Dim = (", dim-i, "|", i, ")" ],
      (*else*)
	DPrint[1, "r = ", rng,  ", Dim = ", dim]
      ];
      dim
   ]

End[]
EndPackage[]

