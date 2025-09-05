(* ::Package:: *)

ClearAll["Global`*"]
Remove["Global`*"]

L = 1;
n = 40;
d = L/n;
iterations = 0;

a = 1;
b = 1;

fuConst = 1;

algo[L_,n_,a_,b_,fuConst_]:=Module[{d, t1=Table[0,{j,0,n},{k,0,n}],t2=Table[0,{j,0,n},{k,0,n}]},
d=L/n;

Clear[tabU, tabV, fv, fu];

eqZ[u_, v_] = 1/2 (fuConst*fu[u]^2 - fv[v]^2); (*-1/2 (fuConst*fu[u]^2+fv[v]^2) for paraboloid, 1/2 (fuConst*fu[u]^2 - fv[v]^2) for hyperbolic paraboloid*)

p = {fu[u], fv[v], eqZ[u, v]};

fu'[x_] := 1/Sqrt[1 + fuConst^2 * fu[x]^2];
fv'[x_] := 1/Sqrt[1 + fv[x]^2];

tabU = Table[{1/2 (fu Sqrt[1 + fuConst^2 fu^2] + ArcSinh[fuConst fu]/fuConst), fu},
            {fu, -60, 60, 0.01}];
fiU = Interpolation[tabU];
fu[x_?NumericQ] := N[fiU[x]];

tabV = Table[{1/2 (fv Sqrt[1 + fv^2] + ArcSinh[fv]), fv}, 
            {fv, -60, 60, 0.01}];
fiV = Interpolation[tabV];
fv[x_?NumericQ] := N[fiV[x]];

\[Phi]=ArcTanh[D[p,u] . D[p,v]];
\[Phi]uv={D[\[Phi],u],D[\[Phi],v]}//Simplify; 

sechsquared\[Phi]=Sech[\[Phi]]^2//Simplify;
sech2\[Phi][u_,v_]=Sech[\[Phi]]^2//Simplify;

tau1u=-sechsquared\[Phi]*\[Phi]uv[[2]]/.v->L; 
tau2v=-sechsquared\[Phi]*\[Phi]uv[[1]]/.u->L;

tau1L=Integrate[tau1u,u]; 
tau2L=Integrate[tau2v,v];

tau12uL=tau1L/.u->L;
tau12Lv=tau2L/.v->L;
tau1uL=(sechsquared\[Phi]/.{u->L,v->L})*a+b(tau1L-tau12uL)//Simplify;
tau2Lv=(sechsquared\[Phi]/.{u->L,v->L})*b+a(tau2L-tau12Lv)//Simplify;


(*T12=Solve[{(T1[u+d,v]-T1[u,v])/d+T2[u,v]pv[u,v]==0,(T2[u,v+d]-T2[u,v])/d+T1[u,v]pu[u,v]==0},{T1[u,v],T2[u,v]}];*)
T12=Solve[{((T1[u+d,v]-T1[u,v])+(T1[u+d,v+d]-T1[u,v+d]))/(2d)+((T2[u,v]+T2[u+d,v]+T2[u,v+d]+T2[u+d,v+d])pv[u+d/2,v+d/2])/4,((T2[u,v+d]-T2[u,v])+(T2[u+d,v+d]-T2[u+d,v]))/(2d)+((T1[u,v]+T1[u+d,v]+T1[u,v+d]+T1[u+d,v+d])pu[u+d/2,v+d/2])/4}==0,{T1[u,v],T2[u,v]}]//Simplify;

T12fd={T1[u,v],T2[u,v]}/.T12[[1]];

t12fd=T12fd/.{
  T1[u_,v_] :> t1dummy[[u/d + 1, v/d + 1]],
  T2[u_,v_] :> t2dummy[[u/d + 1, v/d + 1]]
};
t12fd=t12fd/.{u->j d, v->k d};

T12jk=t12fd/.d->L/n//Simplify;


T12jkSub[j_,k_]=T12jk/.{j->N[j], k->N[k], pu[u_,v_]->\[Phi]uv[[1]],pv[u_,v_]->\[Phi]uv[[2]]}//Simplify; 
tau1uL=(sechsquared\[Phi]/.{u->L,v->L})*a+b(tau1L-tau12uL)/.L->N[L]//Simplify; 
tau2Lv=(sechsquared\[Phi]/.{u->L,v->L})*b+a(tau2L-tau12Lv)/.L->N[L]//Simplify; 
Do[val=N[j*d]; 
t1[[n+1,j+1]]=Evaluate[N[sechsquared\[Phi]/.{u->L, v->val}]*a];
t2[[n+1,j+1]]=Evaluate[N[tau2Lv/.v->val]]; 
t1[[j+1,n+1]]=Evaluate[N[tau1uL/.u->val]]; 
t2[[j+1,n+1]]=Evaluate[N[sechsquared\[Phi]/.{u->val, v->L}]*b]; 
,{j,0,n}];


Do[Do[
iterations=iterations+1;

index1 = 2+j;
index2 = 1+k;
index3 = 1+j;
index4 = 2+k;

t1dummy[[index1,index2]]=t1[[Round[index1],Round[index2]]];
t2dummy[[index3,index4]]=t2[[Round[index3],Round[index4]]];

expr1=T12jkSub[j,k][[1]]/.{
  t1dummy[[aa_,bb_]] :> t1[[Round[aa],Round[bb]]],
  t2dummy[[aa_,bb_]] :> t2[[Round[aa],Round[bb]]]
};

expr2=T12jkSub[j,k][[2]]/.{
  t1dummy[[aa_,bb_]] :> t1[[Round[aa],Round[bb]]],
  t2dummy[[aa_,bb_]] :> t2[[Round[aa],Round[bb]]]
};

t1[[j+1,k+1]]=Evaluate[N[expr1]];
t2[[j+1,k+1]]=Evaluate[N[expr2]];

If[Mod[iterations, 10000]==0, Print["Iterations=", iterations]];
,{k,n-1,0,-1}],{j,n-1,0,-1}];{t1,t2}]

sol=algo[L, n, a, b, fuConst];
T11=sol[[1]];
T22=sol[[2]];

tension[T_] := Table[
  Module[{u, v, val},
    uCoord = d*(i-1);
    vCoord = d*(j-1);
    val = T[[i, j]] / sech2\[Phi][uCoord, vCoord];
    val
  ],
  {i, Length[T]}, {j, Length[T[[1]]]}
];

Print["Tension T1 at origin=", T11[[1,1]]];
Print["Tension T2 at origin=", T22[[1,1]]];

T11Coords=T11;
T22Coords=T22;
T11Coords=Reverse /@ Reverse[Transpose[T11]]//(Reverse /@ # &);
T22Coords=Reverse /@ Reverse[Transpose[T22]]//(Reverse /@ # &);


ru[u_,v_]=D[p,u];
ruu[u_,v_]=D[ru[u,v],u];
rv[u_,v_]=D[p,v];
rvv[u_,v_]=D[rv[u,v],v];

nVec[u_,v_]=Cross[ru[u,v],rv[u,v]];
LL[u_,v_]=ruu[u,v] . nVec[u,v];
NN[u_,v_]=rvv[u,v] . nVec[u,v];

R=ConstantArray[0, Dimensions[T11]];

T11Rotate=Map[Function[col, Reverse[col]], Transpose[T11Coords]]//Transpose;
T22Rotate=Map[Function[col, Reverse[col]], Transpose[T22Coords]]//Transpose;


Do[Do[valU=N[u*d];
valV=N[v*d];
R[[u+1,v+1]]=Evaluate[N[-LL[valU,valV] T11Rotate[[u+1,v+1]]-NN[valU,valV] T22Rotate[[u+1,v+1]]]];
,{v,0,n,1}],{u,0,n,1}];

Show[
ListDensityPlot[
  R,
  DataRange -> {{0, L}, {0, L}},
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange->All,
  FrameLabel -> {
  Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
  Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  PlotLegends->
  BarLegend[{"TemperatureMap", MinMax[R]}, 
    LegendLabel -> "R", 
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendMarkerSize -> {15, 225}
  ]
],
  AspectRatio -> 1,
  ImageSize -> 400
]

RCoords=Reverse[R];

Print["Min/Max of reaction force R=", MinMax[R]];

{rmin, rmax} = MinMax[R];
Return[MinMax[R]];

posMin = Position[R, rmin];
posMax = Position[R, rmax];

coordsMin = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMin);
coordsMax = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMax);

Print["Min value: ", rmin, " at spatial coords: ", coordsMin];
Print["Max value: ", rmax, " at spatial coords: ", coordsMax];


Rresults = Table[
   Module[{Rmat, T11, T22, minR, maxR, d, n},
     n=40;
     d=L/n;
	 sol = algo[L, n, a, b, 1];
	 T11 = sol[[1]];
	 T22 = sol[[2]];
     
     T11=tension[T11];
	 T22=tension[T22];
     T11Coords=Reverse /@ Reverse[Transpose[T11]]//(Reverse /@ # &);
	 T22Coords=Reverse /@ Reverse[Transpose[T22]]//(Reverse /@ # &);
	 T11Rotate=Map[Function[col, Reverse[col]], Transpose[T11Coords]]//Transpose;
	 T22Rotate=Map[Function[col, Reverse[col]], Transpose[T22Coords]]//Transpose;
	 
     Rmat = Table[
       -LL[u*d, v*d]*T11Rotate[[u+1, v+1]] - NN[u*d, v*d]*T22Rotate[[u+1, v+1]],
       {u, 0, n}, {v, 0, n}
     ];
     
     minR = Min[Rmat]; maxR = Max[Rmat];
     Print["L=", L, " R min=", minR, " max=", maxR];
     
     
     {T1min, T1max} = MinMax[T11Rotate];

	 posMinT1 = Position[T11Rotate, T1min];
	 posMaxT1 = Position[T11Rotate, T1max];
	
	 coordsMinT1 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMinT1);
	 coordsMaxT1 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMaxT1);
	
	 Print["L=", L, " Min Value T1=", T1min, " Min at spatial coords: ", coordsMinT1];
	 Print["L=", L, " Max Value T1=", T1max, " Max at spatial coords: ", coordsMaxT1];
	
	 {T2min, T2max} = MinMax[T22Rotate];
	
	 posMinT2 = Position[T22Rotate, T2min];
	 posMaxT2 = Position[T22Rotate, T2max];
	
	 coordsMinT2= ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMinT2);
	 coordsMaxT2 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMaxT2);
	
	 Print["L=", L, " Min Value T2=", T2min, " Min at spatial coords: ", coordsMinT2];
	 Print["L=", L, " Max Value T2=", T2max, " Max at spatial coords: ", coordsMaxT2];
     
     {L, minR, maxR}
   ],
   {L, 1, 6.1, 1} (*specify what parameter we want to change here*)
];

vals = Rresults[[All, 1]];
minVals = Rresults[[All, 2]];
maxVals = Rresults[[All, 3]];

ListLinePlot[
  {
    Transpose[{vals, minVals}],
    Transpose[{vals, maxVals}]
  },
  PlotStyle -> {
    {Blue, Thick},
    {Red, Thick}
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  PlotLegends -> Placed[{Style[Subscript["R", "min"], 14], Style[Subscript["R", "max"], 14]},{0.85,0.4}],
  Frame -> True,
  FrameLabel -> {
    Style["L", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["R", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  GridLines -> Automatic,
  GridLinesStyle -> Directive[LightGray, Thin],
  ImageSize -> 400
]

\[Gamma]angle[u_, v_] := ArcCos[ru[u,v] . rv[u,v]]

\[Gamma]Min = Min[Table[\[Gamma]angle[u, v]*180/\[Pi], {u, 0, L, L/n}, {v, 0, L, L/n}]];
\[Gamma]Max = Max[Table[\[Gamma]angle[u, v]*180/\[Pi], {u, 0, L, L/n}, {v, 0, L, L/n}]];

\[Gamma]Func[L_]:=180-ArcSin[Sqrt[1+2fu[L]^2]/(1+fu[L]^2)]*180/\[Pi] (*\[Gamma] for paraboloid, \[Pi]-\[Gamma] for parabolic hyperboloid*)

DensityPlot[
  \[Gamma]angle[u, v]*180/\[Pi],
  {u, 0, L}, {v, 0, L},
  PlotRange -> All,
  ColorFunction -> "TemperatureMap",
  ColorFunctionScaling -> True,
  PlotLegends -> BarLegend[
    {"TemperatureMap", {\[Gamma]Min, \[Gamma]Max}},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> "\[Gamma] (degrees)",
    LegendMarkerSize -> {15, 225}
  ],
  ImageSize -> 400,
  Frame -> True,
  FrameLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
]

minmax\[Gamma][L_?NumericQ] := Module[{grid, vals},
  grid = Flatten[Table[{u, v}, {u, 0, L, L/n}, {v, 0, L, L/n}], 1];
  vals = \[Gamma]angle @@@ grid;
  Max[vals]*180/\[Pi] (*Min for paraboloid, max for hyperbolic paraboloid*)
];

Ls = Range[0.5, 10, 0.5];

minmaxVals = Table[minmax\[Gamma][L], {L, Ls}];

Legended[
  Show[
    {
      ListLinePlot[
        Transpose[{Ls, minmaxVals}],
        PlotStyle -> Blue
      ],
      Plot[
        \[Gamma]Func[L],
        {L, Min[Ls], Max[Ls]},
        PlotStyle -> {Red, Dashed}
      ]
    },
    Frame -> True,
    FrameLabel -> {
      Style["L", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style["Maximum \[Gamma]", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    },
    GridLines -> Automatic,
    GridLinesStyle -> {LightGray, Thin},
    ImageSize -> 400,
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
  ],
  Placed[
    LineLegend[
      {
        Directive[Blue],
        Directive[Red, Dashed]
      },
      {"Numerical", "Semi-Analytic"},
      LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 14, Black}
    ],
    {0.75, 0.2}
  ]
]


plot1=Flatten[Table[{d*j, d*k,T11[[j+1,k+1]]},{j,0,n},{k,0,n}],1];
pl1=ListPlot3D[plot1,PlotRange -> All,TicksStyle->Directive[FontFamily->"Latin Modern Roman" ],AxesLabel->Table[Style[q,FontFamily->"Latin Modern Roman",FontSize->14],{q,{u,v,T1}}]]


tensionData2DT1=Flatten[Table[{(i-1)d, (j-1)d, T11[[i,j]]}, {i,1,n+1}, {j,1,n+1}], 1];

tensionInterpT1=Interpolation[tensionData2DT1];

Print["Min/Max of tension T1=", MinMax[tensionData2DT1[[All,3]]]];

tensionData2DT2 = Flatten[Table[{(i-1)d, (j-1)d, T22[[i,j]]},{i,1,n+1}, {j,1,n+1}],1];

tensionInterpT2=Interpolation[tensionData2DT2];

Print["Min/Max of tension T2=", MinMax[tensionData2DT2[[All,3]]]];

{T1min, T1max} = MinMax[T11Rotate];

posMinT1 = Position[T11Rotate, T1min];
posMaxT1 = Position[T11Rotate, T1max];

coordsMinT1 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMinT1);
coordsMaxT1 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMaxT1);

Print["Min T1 value: ", T1min, " at spatial coords: ", coordsMinT1];
Print["Max T1 value: ", T1max, " at spatial coords: ", coordsMaxT1];

{T2min, T2max} = MinMax[T22Rotate];

posMinT2 = Position[T22Rotate, T2min];
posMaxT2 = Position[T22Rotate, T2max];

coordsMinT2= ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMinT2);
coordsMaxT2 = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMaxT2);

Print["Min T2 value: ", T2min, " at spatial coords: ", coordsMinT2];
Print["Max T2 value: ", T2max, " at spatial coords: ", coordsMaxT2];

results = Table[
   Module[{tens, t1min, t1max, t2min, t2max},
     soln = algo[L, n, a, b, fuConst];
     tens1 = soln[[1]];
     tens2 = soln[[2]];
     {t1min, t1max} = MinMax[tens1];
     {t2min, t2max} = MinMax[tens2];
     {L, t1min, t1max, t2min, t2max}
   ],
   {L, 1, 6.1, 2} (*Specify what parameter we want to change here*)
];

xValues = results[[All, 1]];
T1minVals  = results[[All, 2]];
T1maxVals  = results[[All, 3]];
T2minVals  = results[[All, 4]];
T2maxVals  = results[[All, 5]];

TableForm[
  Transpose[{xValues, T1minVals, T1maxVals}],
  TableHeadings -> {None, {"L", "T1min", "T1max"}}
]

TableForm[
  Transpose[{xValues, T2minVals, T2maxVals}],
  TableHeadings -> {None, {"L", "T2min", "T2max"}}
]


ListLinePlot[
  {
    Transpose[{xValues, T1minVals}],
    Transpose[{xValues, T2maxVals}]
  },
  PlotStyle -> {
    {Blue, Thick},
    {Red, Thick}  
  },
  PlotLegends -> Placed[{Style[Subscript["T", "1 min"], 14], Style[Subscript["T", "2 max"], 14]},{0.85,0.4}],
  Frame -> True,
  FrameLabel -> {
    Style["L", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["T", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  GridLines -> Automatic,
  GridLinesStyle -> Directive[LightGray, Thin],
  PlotRange->All,
  ImageSize -> 400
]


T00[L_,n_]:=algo[L, n, a, b, fuConst][[1,1,1]];
T0LnumericValue[L_,n_]:=algo[L, n, a, b, fuConst][[1,1,n+1]];

T0n=Table[{n,T00[L,n]},{n,20,61,20}];
(*T0d={L/Transpose[T0n][[1]],Transpose[T0n][[2]]}//Transpose;*) (*Linear Convergence for first-order Scheme*)
T0d={L^2/Transpose[T0n][[1]]^2,Transpose[T0n][[2]]}//Transpose; (*Quadratic Convergence for second-order scheme*)

len=Length[T0d];
line=Solve[(y-T0d[[len,2]])/(x-T0d[[len,1]])==(T0d[[1,2]]-T0d[[len,2]])/(T0d[[1,1]]-T0d[[len,1]]),y]//FullSimplify;
fittedFunc[x_]:=y/.line[[1]];
yMin = (fittedFunc[x]/.x -> 0);
yMax = fittedFunc[x]/.x->T0d[[1,1]];
Show[
  ListPlot[
    T0d,
	PlotRange -> {{0, T0d[[1, 1]]}, {yMin, yMax}},
    Frame -> True,
    GridLines -> Automatic,
    GridLinesStyle -> Directive[LightGray, Thin],
    FrameTicksStyle -> Directive[FontFamily -> "Latin Modern Roman"],
    PlotRangePadding -> None,
    PlotStyle -> {Blue, PointSize[0.015]},
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
    FrameLabel -> {
      Style[Row[{"\!\(\*SuperscriptBox[\(\[Delta]\), \(2\)]\)=", L, "\[ThinSpace]/\[ThinSpace]\!\(\*SuperscriptBox[\(n\), \(2\)]\)"}], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style[Row[{Subscript["T", 1], "(0,0)"}], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    }
  ],
  Plot[
    fittedFunc[x],
    {x, 0, T0d[[1, 1]]},
    PlotStyle -> {Red, Dashed}
  ],
  ImageSize->400
]

Print["y-intercept = ", yMin];


(*For hyperbolic paraboloid*)
T0Lexpr[L_]:=(2+3 fiU[L]^2)/(2(1+fiU[L]^2)^2);

Lmin=1;
Lmax=10.1;
Lstep=2;


T0L=Table[{L, T0Lexpr[L]},{L, Lmin, Lmax, Lstep*0.1}]
T0Lnumeric=Table[{L, T0LnumericValue[L, Round[L*10]]},{L, Lmin, Lmax, Lstep}];
T0vsL=Table[{L, T00[L, Round[L*10]]},{L, Lmin, Lmax, Lstep}];

minT00=MinimalBy[T0vsL, Last];
maxT00=MaximalBy[T0vsL, Last];
Print["Min of T1(0,0)=",minT00];
Print["Max of T1(0,0)=",maxT00];

minT0L=MinimalBy[T0L, Last];
maxT0L=MaximalBy[T0L, Last];
Print["Min of T1(0,L)=",minT0L];
Print["Max of T1(0,L)=",maxT0L];

minT0Lnumeric=MinimalBy[T0Lnumeric, Last];
maxT0Lnumeric=MaximalBy[T0Lnumeric, Last];
Print["Min of T1(0,L) numeric=",minT0Lnumeric];
Print["Max of T1(0,L) numeric=",maxT0Lnumeric];

ListPlot[
  {T0vsL, T0L, T0Lnumeric},
  Joined -> True,
  PlotStyle -> {
    {Red, Dashed, Thick},
    {Blue, Dotted, Thick},
    {Green, Thick}
  },
  PlotRange -> All,
  Frame -> True,
  FrameLabel -> {
    Style["L", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style[Subscript["T", 1], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  FrameTicksStyle -> Directive[FontFamily -> "Latin Modern Roman"],
  PlotRangePadding -> None,
  ImageSize -> 400,
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  GridLines -> Automatic,
  GridLinesStyle -> Directive[LightGray, Thin],
  PlotLegends -> Placed[
    {
      Style[Row[{Subscript["T", 1], "(0,0) numeric"}], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style[Row[{Subscript["T", 1], "(0,L) analytic"}], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style[Row[{Subscript["T", 1], "(0,L) numeric"}], FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    },
    {0.75, 0.78}
  ]
]

Plot[fiU[f], {f, -L, L}, PlotPoints -> 50, PlotLabel->Style[Subscript["f",u], FontFamily -> "Latin Modern Roman", FontSize->14]]
Plot[fiV[f], {f, -L, L}, PlotPoints -> 50, PlotLabel->Style[Subscript["f",v], FontFamily -> "Latin Modern Roman", FontSize->14]]

Plot3D[eqZ[u,v], {u, -L, L}, {v, -L, L},
   PlotPoints -> 50, 
   MaxRecursion -> 0, 
   AxesLabel -> {"u", "v", "z(u,v)"}, 
   TicksStyle -> Directive[FontFamily -> "Latin Modern Roman", Black],
   PlotRange -> All
]

(*2D tension plot*)
(*T1*)
ListDensityPlot[
  tensionData2DT1,
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange -> All,
  FrameLabel -> {
  Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
  Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  PlotLegends -> 
    BarLegend[{"TemperatureMap", MinMax[tensionData2DT1[[All, 3]]]}, 
      LegendLabel -> Subscript["T", 1], 
      LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
      LegendMarkerSize -> {15, 225}
    ],
    ImageSize -> 400
]


(*T2*)
ListDensityPlot[
  tensionData2DT2,
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange -> All,
  FrameLabel -> {
  Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
  Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  PlotLegends -> 
    BarLegend[{"TemperatureMap", MinMax[tensionData2DT2[[All, 3]]]}, 
      LegendLabel -> Subscript["T", 2],
      LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
      LegendMarkerSize -> {15, 225}
    ],
    ImageSize -> 400
]

(*3D tension plot*)
(*T1*)
z[u_?NumericQ, v_?NumericQ] := eqZ[u,v];

data3DT1 = Flatten[
  Table[{(i-1)d, (j-1)d, z[(i-1)d,(j-1)d], T11[[i, j]]},
    {i, 1, n + 1}, {j, 1, n + 1}
  ],
  1
];

tensionInterpT1 = Interpolation[
  data3DT1[[All, {1, 2, 4}]] /. {u_, v_, tension_} :> {{u, v}, tension}
];

minTensionT1 = Min[data3DT1[[All, 4]]];
maxTensionT1 = Max[data3DT1[[All, 4]]];

colourFuncT1=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT1[x, y], {minTensionT1, maxTensionT1}]]
];

Legended[
  Plot3D[
    z[u, v],
    {u, 0, L}, {v, 0, L},
    ColorFunction -> colourFuncT1,
    Mesh -> None,
    ColorFunctionScaling -> False,
    PlotRange -> All,
    ImageSize -> 400,
    AxesLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
    Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    },
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
  ],
  BarLegend[
    {"TemperatureMap", {minTensionT1, maxTensionT1}},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 1],
    LegendMarkerSize -> {15, 225}
  ]
]


allQuadrantsDataT1 = Join[
  tensionData2DT1,                           
  tensionData2DT1 /. {u_, v_, t_} :> {-u, v, t},
  tensionData2DT1 /. {u_, v_, t_} :> {u, -v, t},
  tensionData2DT1 /. {u_, v_, t_} :> {-u, -v, t}
];

allQuadrantsDataT1 = DeleteDuplicates[allQuadrantsDataT1, #1[[1 ;; 2]] == #2[[1 ;; 2]] &];
tensionInterpT1All=Interpolation[allQuadrantsDataT1];


colourFuncAllT1=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT1All[x, y], {minTensionT1, maxTensionT1}]]
];

tensionPlotT1=Legended[
  Plot3D[
  eqZ[u,v],
  {u, -L, L}, {v, -L, L},
  Mesh->None,
  ColorFunction -> colourFuncAllT1, 
  ColorFunctionScaling -> False,
  PlotStyle -> PointSize[Medium],
  PlotRange -> All,
  ImageSize -> 400,
  AxesLabel -> {
  Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
  Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
  Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
],
  BarLegend[
    {"TemperatureMap", {minTensionT1, maxTensionT1}}, (*TemperatureMap*)
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 1],
    LegendMarkerSize -> {15, 225}
  ]
]

(*T2*)
data3DT2 = Flatten[
  Table[{(i-1)d, (j-1)d, z[(i-1)d,(j-1)d], T22[[i, j]]},
    {i, 1, n+1}, {j, 1, n+1}
  ],
  1
];

tensionInterpT2 = Interpolation[
  data3DT2[[All, {1, 2, 4}]] /. {u_, v_, tension_} :> {{u, v}, tension}
];

minTensionT2 = Min[data3DT2[[All, 4]]];
maxTensionT2 = Max[data3DT2[[All, 4]]];

tensionData2DT2 = Flatten[
  Table[
    {(i-1)d, (j-1)d, T22[[i,j]]},
    {i,1,n+1}, {j,1,n+1}
  ],1
];

colourFuncT2=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT2[x, y], {minTensionT2, maxTensionT2}]]
];

Legended[
  Plot3D[
    z[u, v],
    {u, 0, L}, {v, 0, L},
    ColorFunction -> colourFuncT2,
    Mesh -> None,
    ColorFunctionScaling -> False,
    PlotRange -> All,
    ImageSize -> 400,
    AxesLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
    Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    },
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
  ],
  BarLegend[
    {"TemperatureMap", {minTensionT2, maxTensionT2}},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 1],
    LegendMarkerSize -> {15, 225}
  ]
]

allQuadrantsDataT2 = Join[
  tensionData2DT2,                             
  tensionData2DT2 /. {u_, v_, t_} :> {-u, v, t},
  tensionData2DT2 /. {u_, v_, t_} :> {u, -v, t},
  tensionData2DT2 /. {u_, v_, t_} :> {-u, -v, t}
];

allQuadrantsDataT2 = DeleteDuplicates[allQuadrantsDataT2, #1[[1 ;; 2]] == #2[[1 ;; 2]] &];
tensionInterpT2All=Interpolation[allQuadrantsDataT2];

colourFuncAllT2=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT2All[x, y], {minTensionT2, maxTensionT2}]]
];

tensionPlotT2=Legended[
  Plot3D[
  eqZ[u,v],
  {u, -L, L}, {v, -L, L},
  Mesh->None,
  ColorFunction -> colourFuncAllT2, 
  ColorFunctionScaling -> False,
  PlotStyle -> PointSize[Medium],
  PlotRange -> All,
  ImageSize -> 400,
  AxesLabel -> {
  Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
  Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black], 
  Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
],
  BarLegend[
    {"TemperatureMap", {minTensionT2, maxTensionT2}},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 2],
    LegendMarkerSize -> {15, 225}
  ]
]

offset=0.02;
length=Sqrt[2L^2];

fibreNum=L/5;

fibresU = Table[
   ParametricPlot3D[
     {u, v, eqZ[u,v]}, {v, -L, L},
     PlotStyle -> {Thickness[0.0025], Darker[Black], Opacity[1]}],
   {u, -L, L, fibreNum}
];

fibresV = Table[
   ParametricPlot3D[
     {u, v, eqZ[u,v]}, {u, -L, L},
     PlotStyle -> {Thickness[0.0025], Darker[Black],Opacity[1]}],
   {v, -L, L, fibreNum}
];

(*surface = ParametricPlot3D[ (*surface used for paraboloid*)
  {\[Rho] Cos[\[Theta]], \[Rho] Sin[\[Theta]], eqZ[\[Rho] Cos[\[Theta]], \[Rho] Sin[\[Theta]]] - offset},
  {\[Rho], 0, length}, {\[Theta], 0, 2 Pi},
  Mesh -> None,
  PlotStyle -> Opacity[0.6, LightGray],
  PlotRange -> All,
  BoxRatios -> {1, 1, 1}
];*)

surface = ParametricPlot3D[ (*surface used for hyperbolic paraboloid*)
  {u, v, eqZ[u, v] - offset},
  {u, -L-0.2, L+0.2}, {v, -L-0.2, L+0.2},
  Mesh -> None,
  PlotStyle -> Opacity[0.6, LightGray],
  PlotRange -> All,
  BoxRatios -> {1, 1, 0.5}
];

Show[
   {surface, fibresU, fibresV, tensionPlotT1},
   PlotRange -> All,
   ImageSize -> 400,
   AxesLabel -> {
     Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
     Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
     Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
   },
   LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
   PlotLegends -> Placed[
     BarLegend[
       {"TemperatureMap", {minTensionT2, maxTensionT2}},
       LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
       LegendLabel -> Subscript["T", 1],
       LegendMarkerSize -> {15, 225}
     ],
     Right
   ]
]

Show[
   {surface, fibresU, fibresV, tensionPlotT2},
   PlotRange -> All,
   ImageSize -> 400,
   AxesLabel -> {
     Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
     Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
     Style["z(u,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
   },
   LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
   PlotLegends -> Placed[
     BarLegend[
       {"TemperatureMap", {minTensionT2, maxTensionT2}},
       LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
       LegendLabel -> Subscript["T", 2],
       LegendMarkerSize -> {15, 225}
     ],
     Right
   ]
]


(* ::Input:: *)
(*Legended[,Placed[\!\(TraditionalForm\`*)
(*FormBox[*)
(*TemplateBox[{FormBox[StyleBox[StyleBox[PaneBox["", Alignment -> Left, AppearanceElements -> None, ImageMargins -> {{5, 5}, {5, 5}}, ImageSizeAction -> "ResizeToFit"], StripOnInput -> False, LineIndent -> 0], StripOnInput -> False, FontFamily -> "Latin Modern Roman", FontSize -> 12, Background -> Automatic], TraditionalForm]},*)
(*"BarLegend",*)
(*DisplayFunction->(#& ),*)
(*InterpretationFunction:>(RowBox[{"BarLegend", "[", RowBox[{RowBox[{"{", RowBox[{"\"ThermometerColors\"", ",", RowBox[{"{", RowBox[{RowBox[{"-", "4.155230209335476`"}], ",", RowBox[{"-", "0.0010859695740529592`"}]}], "}"}]}], "}"}], ",", RowBox[{"LabelStyle", "->", RowBox[{"Directive", "[", RowBox[{RowBox[{"FontSize", "->", "12"}], ",", RowBox[{"FontFamily", "->", "\"Latin Modern Roman\""}]}], "]"}]}], ",", RowBox[{"LegendLabel", "->", "\"R\""}], ",", RowBox[{"LegendLayout", "->", "\"Column\""}], ",", RowBox[{"LegendMarkerSize", "->", "225"}], ",", RowBox[{"Charting`AxisLabel", "->", "None"}], ",", RowBox[{"Charting`TickSide", "->", "Right"}], ",", RowBox[{"ColorFunctionScaling", "->", "True"}]}], "]"}]& )],*)
(*TraditionalForm]\),After]]*)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Message:: *)
(*ListPlot::lpn*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Message:: *)
(*Do::nliter*)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Message:: *)
(*ListPlot::nonopt*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(* *)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Legended[,Placed[\!\(TraditionalForm\`*)
(*FormBox[*)
(*TemplateBox[{FormBox["", TraditionalForm]},*)
(*"BarLegend",*)
(*DisplayFunction->(#& ),*)
(*InterpretationFunction:>(RowBox[{"BarLegend", "[", RowBox[{RowBox[{"{", RowBox[{RowBox[{RowBox[{InterpretationBox[RowBox[{TagBox["ColorDataFunction", "SummaryHead"], "[", DynamicModuleBox[{Typeset`open$$ = False, Typeset`embedState$$ = "Ready"}, TemplateBox[{PaneSelectorBox[{False -> GridBox[{{PaneBox[ButtonBox[DynamicBox[FEPrivate`FrontEndResource["FEBitmaps", "SummaryBoxOpener"]], ButtonFunction :> (Typeset`open$$ = True), Appearance -> None, BaseStyle -> {}, Evaluator -> Automatic, Method -> "Preemptive"], Alignment -> {Center, Center}, ImageSize -> Dynamic[{Automatic, 3.5 (CurrentValue["FontCapHeight"]/AbsoluteCurrentValue[Magnification])}]], GridBox[{{RowBox[{TagBox["\"Name: \"", "SummaryItemAnnotation"], " ", TagBox["\"TemperatureMap\"", "SummaryItem"]}]}, {RowBox[{TagBox["\"Gradient: \"", "SummaryItemAnnotation"], " ", TagBox[StyleBox[GraphicsBox[{RasterBox[CompressedData["*)
(*1:eJwVlXk41nkXxm1ZIyVFDAkZQqQiS3dSyhIpZZsWJNmXZKtISaUik2w1Q4VE*)
(*SkoUlcmS3WPPvj6WZ/l9bTNRqvd5/zjXOf+c61znPtfnPgoufofceLm4uLg5*)
(*4caJ/9fVN14Er56oxlXjVNO7N9tQIb7jotEgG7Qp3LpFr8GP3pjGruR2rBVI*)
(*/xU1zkaPGe0h31gdgoKDbGUzO+D1g+9yNZuNsacniy+MNIAl7tJ7sqATH+c8*)
(*+UT+ZYMSmmmYH2rCqTxrl6yyLkgwaDHWS2wsvd4V8MaPhr69RlNTNV/gPrRd*)
(*KJGXAjdd8MKsbwtsh9T8NTu6Udr54OYXYQr8ki0xmr6taAiX+ho43IMVjTxi*)
(*v62iILI3NcHTpw0mkvwRxexeuFacueMsTcHawZe+FNkOudqffXuYfZA0NNnV*)
(*pUDh1WDtMf0HHXgm9ONJ8HA//vu3K4auRmHNaeXOkJJO7DD/HpjTNYCuF96N*)
(*czoUwlmXrIrau1Adu2jU0ziIEg/u1TxGFAYC+6pnp78gl36ej99lCCmKSY7i*)
(*phSMF3WhJdqD6WXfp+T6hxDWr/ZQzppCZuTdYh/VXuhuDG/WtR+GY/LHCXV7*)
(*CoL8ZHPe3j5cNF18fbBtGAY2tpoGzhRGDljaiEb2Q9BFIjTPbgS9BQZrlb0p*)
(*PJHKryyZHYB0kOt/N6gRfHOq2VMdTqF4hl92i84Q1GJeBZ25OgopgSOB7jco*)
(*rLMr7hBgD8EghXfOVHYMuoXD6YIpFC6Wucf3Zw/DMvdwgPKrMRw95tv4NJvC*)
(*kIKU2auTIzhe9pjwmtMRJPj9m3kRBZNrNTw31o3Cr2nOZ2SIjruvrv3OqqCQ*)
(*zQotO94+iktDJqzykHG8PL766O1WCkKHVIO3xo0hYfauZ7rYBGhCD69oDlOI*)
(*uJtt3GJIh4+DE59g8gSkppQG781SmG1XFPVl0mFevuFvf/lJnKzJ0f/BS3B6*)
(*zcMvwmnj2KjC0O1+MomnT9STTkkS9NjJZT7ZPwGeuJctxlpTmIkpmKnfSGCV*)
(*et9vz9cJDMyHeuWWTGHH6a0HdPQIKnqkDIazJlHqtGuZhDEDUXtLctLMCHRl*)
(*k/gjbKeQ/Ekg/XwtA7VKhnw8TgTPjkm0ruNlIEi1WW/MholVfOUnPLwJ4vut*)
(*u5RuMBBsH+HdXsqEaG69dmAYwdMlrzD6NwZuein4XF/DgouOzEeLaM5cmesy*)
(*2d5MpEdU+hgGsFBc5mmpHE/Qr5/5/vQAE68T3H2n61lYbvqu+2cqwYJD+QmV*)
(*gyzUZQr7ZW5kw6VZyP1LJsGqsD7uyX9YGCzO97OPYqPY3mH+5QsC9ZSFxzk6*)
(*bMzXHfRf3sfG8pGcqJvvCPYVrzb1yGJDaGDOv3w7BWevBTG3KgLVjFLGBm4K*)
(*PIYH96yKpHDPVXL03UuCB7KhiU1aFKo3y79Pf0QhekfjHiFnArHUrTvDT1KI*)
(*VaS2aVRTCFpxNdtOnCBKcmZC+Q6FA2vfP383RcGVbiiY/ZHCfEJ+QgsnrxS5*)
(*pbJflOBw6bzHvC+F02KeBhcJhfafjhkdWgQmCc/qd8tR6I7dSP9dniBlVlXa*)
(*1ZZAx/2URkIjGxYCo3HtVgRO4wsJ0yEEG4xk4wcvsPHhSrrepQgC+Z7PwhH3*)
(*ObpItE9rqLMRX+8r636DYPm7RGWuDAJLYaNnUSEsOEvs5LJKJFhMdd51maNj*)
(*DHe2e8cnJrY4iY5tTScYD9N04ntK8M+CmKKqGBO8j/s+y+QStDl8PxeTT/Cd*)
(*hAxccGCgg5GXx1NEUL6j5o5gIcG2iaFUWuYUsrecj5/6SJAvfS8v9g2B/4DZ*)
(*EaXpSYSGm5+l1RGkLTpXLy8lyO0oFA81mITZJ2kOkQTXujWH4zh94w0yDfUx*)
(*E1jnQne71sWZa8O2U3tPECfzQsUuehxMjc3CDe0EB5IyLxwqJmDcszv805GO*)
(*ssXQ5+KtBJ97nB6Gc+63T5wrMkt7DLerPh060kywW16i+lEewePYnFxLwVEc*)
(*T1j+NbWBoMy1jlGXRcC1zKZzbmAYm48dvT9Qy+EgJ2rFHEePPyIXue8XDYFL*)
(*NQOKnwlesvS2yqQRBM6ZOEVLDaJlfmrUvZJgk/a0vQlH102TiYWtVX344Y2g*)
(*B5z9w+ZfhH9zJzgbIt1h29eDYaNnfQV/EgQUXUpqpii0GCyL21nVjSox6b1V*)
(*vgQewTaFmecoaHHNmP7+/AtyBq/md5sTOOtuaArj/Im4yr5fK5O7cKtgVpLi*)
(*8O20MDtldYWN6es1Jd8jO+EfdSKCh+MTh99WLFMSZsP6wOsA+pkO2B5qGF8z*)
(*SMEiPFFh8Q4Lz1dmqDXbtENXcYf1plKOnxm4GTWt5XDXeXO0RL8NMvNZxUim*)
(*YLC0zeHx30x4pYU8eKTYioQj+mzXUxy/tLuuy9XBgOSJy7frWlogWNy04bo2*)
(*hQ+FPZLHRBj4qHg7YjayBRFSrvbPfrLBJaYx/9Z4Ch6TyX7rNFswH/b1Nq2e*)
(*DWOPyNY1oZOQyH90cncfDV69NyvmU9i4UtlScPb5BD4E5Nt4xtIwbLh+Ueo0*)
(*G5XySvG0sXGc2V6y+089Guz/fq1pxOGd/3ywj4bMOJT+u+oe1NiMpl/7Tzlz*)
(*sbGvs8Yi1oaO0Mj7ZpWqzZgWMWhya2GBJpa+cuHqGBZVnqgvxjXBne10yDGT*)
(*hYVtuha+b0chNqRxJ2OhEQNNFzqtONysP9YcPcYagWLK67l9Lo04UvCXo4k5*)
(*C2bR7h8c149A76CBHalvQH3ChwHd31gIyPv1lXZ4GFaCn94lbWvA7rODLurT*)
(*TKS1JmvvuzYE1/L9cjvT6/HWlmtifQUT0XMnOsPPDSI0tDmKLlgPre0KXpJJ*)
(*TLQb3zFz7+vHba2j9FuBdVD1l9RL9mTiL4FRy5KlXmhzX1Qr76mFilNBks5u*)
(*JhzKwv1b47sxxzO2RWRXLZRMLf5tlmZiTcCqRNaGLhTxWRgczaqBgvb4Ye8Z*)
(*BtqUc4v537QjmL/Q5KFwDeRlowoFOb6f3GPcu96sFfqC0pYsv8/4TUB2ZVYG*)
(*Azlyr36cK2nGktAlW92OaqybfeNnHMqAwvWRPbkDdfggMvHHZf1qSPXbNPVb*)
(*M5A2s/LWAF81IkWt3BrTqyBZw1IPV2FgtZNx26pN/8B4RZGP1LIq/A+f0N5y*)
(**)
(*"], {{0, 0}, {1, 1}}]}, {ImageSize -> 65, BaselinePosition -> Bottom, AspectRatio -> NCache[Rational[1, 8], 0.125], PlotRange -> {{0, 1}, {0, 1}}}], Selectable -> False, StripOnInput -> False], "SummaryItem"]}]}}, GridBoxAlignment -> {"Columns" -> {{Left}}, "Rows" -> {{Automatic}}}, AutoDelete -> False, GridBoxItemSize -> {"Columns" -> {{Automatic}}, "Rows" -> {{Automatic}}}, GridBoxSpacings -> {"Columns" -> {{2}}, "Rows" -> {{Automatic}}}, BaseStyle -> {ShowStringCharacters -> False, NumberMarks -> False, PrintPrecision -> 3, ShowSyntaxStyles -> False}]}}, GridBoxAlignment -> {"Columns" -> {{Left}}, "Rows" -> {{Top}}}, AutoDelete -> False, GridBoxItemSize -> {"Columns" -> {{Automatic}}, "Rows" -> {{Automatic}}}, BaselinePosition -> {1, 1}], True -> GridBox[{{PaneBox[ButtonBox[DynamicBox[FEPrivate`FrontEndResource["FEBitmaps", "SummaryBoxCloser"]], ButtonFunction :> (Typeset`open$$ = False), Appearance -> None, BaseStyle -> {}, Evaluator -> Automatic, Method -> "Preemptive"], Alignment -> {Center, Center}, ImageSize -> Dynamic[{Automatic, 3.5 (CurrentValue["FontCapHeight"]/AbsoluteCurrentValue[Magnification])}]], GridBox[{{RowBox[{TagBox["\"Name: \"", "SummaryItemAnnotation"], " ", TagBox["\"TemperatureMap\"", "SummaryItem"]}]}, {RowBox[{TagBox["\"Gradient: \"", "SummaryItemAnnotation"], " ", TagBox[StyleBox[GraphicsBox[{RasterBox[CompressedData["*)
(*1:eJwVlXk41nkXxm1ZIyVFDAkZQqQiS3dSyhIpZZsWJNmXZKtISaUik2w1Q4VE*)
(*SkoUlcmS3WPPvj6WZ/l9bTNRqvd5/zjXOf+c61znPtfnPgoufofceLm4uLg5*)
(*4caJ/9fVN14Er56oxlXjVNO7N9tQIb7jotEgG7Qp3LpFr8GP3pjGruR2rBVI*)
(*/xU1zkaPGe0h31gdgoKDbGUzO+D1g+9yNZuNsacniy+MNIAl7tJ7sqATH+c8*)
(*+UT+ZYMSmmmYH2rCqTxrl6yyLkgwaDHWS2wsvd4V8MaPhr69RlNTNV/gPrRd*)
(*KJGXAjdd8MKsbwtsh9T8NTu6Udr54OYXYQr8ki0xmr6taAiX+ho43IMVjTxi*)
(*v62iILI3NcHTpw0mkvwRxexeuFacueMsTcHawZe+FNkOudqffXuYfZA0NNnV*)
(*pUDh1WDtMf0HHXgm9ONJ8HA//vu3K4auRmHNaeXOkJJO7DD/HpjTNYCuF96N*)
(*czoUwlmXrIrau1Adu2jU0ziIEg/u1TxGFAYC+6pnp78gl36ej99lCCmKSY7i*)
(*phSMF3WhJdqD6WXfp+T6hxDWr/ZQzppCZuTdYh/VXuhuDG/WtR+GY/LHCXV7*)
(*CoL8ZHPe3j5cNF18fbBtGAY2tpoGzhRGDljaiEb2Q9BFIjTPbgS9BQZrlb0p*)
(*PJHKryyZHYB0kOt/N6gRfHOq2VMdTqF4hl92i84Q1GJeBZ25OgopgSOB7jco*)
(*rLMr7hBgD8EghXfOVHYMuoXD6YIpFC6Wucf3Zw/DMvdwgPKrMRw95tv4NJvC*)
(*kIKU2auTIzhe9pjwmtMRJPj9m3kRBZNrNTw31o3Cr2nOZ2SIjruvrv3OqqCQ*)
(*zQotO94+iktDJqzykHG8PL766O1WCkKHVIO3xo0hYfauZ7rYBGhCD69oDlOI*)
(*uJtt3GJIh4+DE59g8gSkppQG781SmG1XFPVl0mFevuFvf/lJnKzJ0f/BS3B6*)
(*zcMvwmnj2KjC0O1+MomnT9STTkkS9NjJZT7ZPwGeuJctxlpTmIkpmKnfSGCV*)
(*et9vz9cJDMyHeuWWTGHH6a0HdPQIKnqkDIazJlHqtGuZhDEDUXtLctLMCHRl*)
(*k/gjbKeQ/Ekg/XwtA7VKhnw8TgTPjkm0ruNlIEi1WW/MholVfOUnPLwJ4vut*)
(*u5RuMBBsH+HdXsqEaG69dmAYwdMlrzD6NwZuein4XF/DgouOzEeLaM5cmesy*)
(*2d5MpEdU+hgGsFBc5mmpHE/Qr5/5/vQAE68T3H2n61lYbvqu+2cqwYJD+QmV*)
(*gyzUZQr7ZW5kw6VZyP1LJsGqsD7uyX9YGCzO97OPYqPY3mH+5QsC9ZSFxzk6*)
(*bMzXHfRf3sfG8pGcqJvvCPYVrzb1yGJDaGDOv3w7BWevBTG3KgLVjFLGBm4K*)
(*PIYH96yKpHDPVXL03UuCB7KhiU1aFKo3y79Pf0QhekfjHiFnArHUrTvDT1KI*)
(*VaS2aVRTCFpxNdtOnCBKcmZC+Q6FA2vfP383RcGVbiiY/ZHCfEJ+QgsnrxS5*)
(*pbJflOBw6bzHvC+F02KeBhcJhfafjhkdWgQmCc/qd8tR6I7dSP9dniBlVlXa*)
(*1ZZAx/2URkIjGxYCo3HtVgRO4wsJ0yEEG4xk4wcvsPHhSrrepQgC+Z7PwhH3*)
(*ObpItE9rqLMRX+8r636DYPm7RGWuDAJLYaNnUSEsOEvs5LJKJFhMdd51maNj*)
(*DHe2e8cnJrY4iY5tTScYD9N04ntK8M+CmKKqGBO8j/s+y+QStDl8PxeTT/Cd*)
(*hAxccGCgg5GXx1NEUL6j5o5gIcG2iaFUWuYUsrecj5/6SJAvfS8v9g2B/4DZ*)
(*EaXpSYSGm5+l1RGkLTpXLy8lyO0oFA81mITZJ2kOkQTXujWH4zh94w0yDfUx*)
(*E1jnQne71sWZa8O2U3tPECfzQsUuehxMjc3CDe0EB5IyLxwqJmDcszv805GO*)
(*ssXQ5+KtBJ97nB6Gc+63T5wrMkt7DLerPh060kywW16i+lEewePYnFxLwVEc*)
(*T1j+NbWBoMy1jlGXRcC1zKZzbmAYm48dvT9Qy+EgJ2rFHEePPyIXue8XDYFL*)
(*NQOKnwlesvS2yqQRBM6ZOEVLDaJlfmrUvZJgk/a0vQlH102TiYWtVX344Y2g*)
(*B5z9w+ZfhH9zJzgbIt1h29eDYaNnfQV/EgQUXUpqpii0GCyL21nVjSox6b1V*)
(*vgQewTaFmecoaHHNmP7+/AtyBq/md5sTOOtuaArj/Im4yr5fK5O7cKtgVpLi*)
(*8O20MDtldYWN6es1Jd8jO+EfdSKCh+MTh99WLFMSZsP6wOsA+pkO2B5qGF8z*)
(*SMEiPFFh8Q4Lz1dmqDXbtENXcYf1plKOnxm4GTWt5XDXeXO0RL8NMvNZxUim*)
(*YLC0zeHx30x4pYU8eKTYioQj+mzXUxy/tLuuy9XBgOSJy7frWlogWNy04bo2*)
(*hQ+FPZLHRBj4qHg7YjayBRFSrvbPfrLBJaYx/9Z4Ch6TyX7rNFswH/b1Nq2e*)
(*DWOPyNY1oZOQyH90cncfDV69NyvmU9i4UtlScPb5BD4E5Nt4xtIwbLh+Ueo0*)
(*G5XySvG0sXGc2V6y+089Guz/fq1pxOGd/3ywj4bMOJT+u+oe1NiMpl/7Tzlz*)
(*sbGvs8Yi1oaO0Mj7ZpWqzZgWMWhya2GBJpa+cuHqGBZVnqgvxjXBne10yDGT*)
(*hYVtuha+b0chNqRxJ2OhEQNNFzqtONysP9YcPcYagWLK67l9Lo04UvCXo4k5*)
(*C2bR7h8c149A76CBHalvQH3ChwHd31gIyPv1lXZ4GFaCn94lbWvA7rODLurT*)
(*TKS1JmvvuzYE1/L9cjvT6/HWlmtifQUT0XMnOsPPDSI0tDmKLlgPre0KXpJJ*)
(*TLQb3zFz7+vHba2j9FuBdVD1l9RL9mTiL4FRy5KlXmhzX1Qr76mFilNBks5u*)
(*JhzKwv1b47sxxzO2RWRXLZRMLf5tlmZiTcCqRNaGLhTxWRgczaqBgvb4Ye8Z*)
(*BtqUc4v537QjmL/Q5KFwDeRlowoFOb6f3GPcu96sFfqC0pYsv8/4TUB2ZVYG*)
(*Azlyr36cK2nGktAlW92OaqybfeNnHMqAwvWRPbkDdfggMvHHZf1qSPXbNPVb*)
(*M5A2s/LWAF81IkWt3BrTqyBZw1IPV2FgtZNx26pN/8B4RZGP1LIq/A+f0N5y*)
(**)
(*"], {{0, 0}, {1, 1}}]}, {ImageSize -> 65, BaselinePosition -> Bottom, AspectRatio -> NCache[Rational[1, 8], 0.125], PlotRange -> {{0, 1}, {0, 1}}}], Selectable -> False, StripOnInput -> False], "SummaryItem"]}]}, {RowBox[{TagBox["\"Domain: \"", "SummaryItemAnnotation"], " ", TagBox[RowBox[{"{", RowBox[{"0", ",", "1"}], "}"}], "SummaryItem"]}]}, {RowBox[{TagBox["\"Class: \"", "SummaryItemAnnotation"], " ", TagBox["\"Gradients\"", "SummaryItem"]}]}}, GridBoxAlignment -> {"Columns" -> {{Left}}, "Rows" -> {{Automatic}}}, AutoDelete -> False, GridBoxItemSize -> {"Columns" -> {{Automatic}}, "Rows" -> {{Automatic}}}, GridBoxSpacings -> {"Columns" -> {{2}}, "Rows" -> {{Automatic}}}, BaseStyle -> {ShowStringCharacters -> False, NumberMarks -> False, PrintPrecision -> 3, ShowSyntaxStyles -> False}]}}, GridBoxAlignment -> {"Columns" -> {{Left}}, "Rows" -> {{Top}}}, AutoDelete -> False, GridBoxItemSize -> {"Columns" -> {{Automatic}}, "Rows" -> {{Automatic}}}, BaselinePosition -> {1, 1}]}, Dynamic[Typeset`open$$], ImageSize -> Automatic]}, "SummaryPanel"], DynamicModuleValues :> {}], "]"}], ColorDataFunction["TemperatureMap", "Gradients", {0, 1}, Blend["TemperatureMap", #]& ], Selectable -> False, Editable -> False, SelectWithContents -> True], "[", "#1", "]"}], "&"}], ",", RowBox[{"{", RowBox[{"0.35523685182885467`", ",", "2.593092565075504`"}], "}"}]}], "}"}], ",", RowBox[{"LabelStyle", "->", RowBox[{"{", "}"}]}], ",", RowBox[{"LegendLayout", "->", "\"Column\""}], ",", RowBox[{"LegendMarkerSize", "->", "225"}], ",", RowBox[{"ScalingFunctions", "->", RowBox[{"{", RowBox[{"Identity", ",", "Identity"}], "}"}]}], ",", RowBox[{"Charting`AxisLabel", "->", "None"}], ",", RowBox[{"Charting`TickSide", "->", "Right"}], ",", RowBox[{"ColorFunctionScaling", "->", "True"}]}], "]"}]& )],*)
(*TraditionalForm]\),After]]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Message:: *)
(*Part::pkspec1*)


(* ::Input:: *)
(**)


(* ::Message:: *)
(*General::stop*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
(**)
