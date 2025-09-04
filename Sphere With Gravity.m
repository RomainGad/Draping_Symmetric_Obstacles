(* ::Package:: *)

ClearAll["Global`*"];
Remove["Global`*"];

L = 1.3; (*Max L=1.36*)
n = 40;
a = 0;
b = 0;
d = L/n;
iterations = 0;

(*Calculate spatial coordinates*)
prog[d_,M_,F_,g_,max_]:=(Do[XX[0,j]=0;
YY[0,j]=g[d j];
XX[j,0]=g[d j];
YY[j,0]=0;
,{j,0,M}];
Do[Do[
XX[i+1,j+1]=
	If[d^2 (i+1)(j+1)<max,
	-((((-YY[i,j]+YY[1+i,j]) (1/2 (-F[Sqrt[XX[i,1+j]^2+YY[i,1+j]^2]]-F[Sqrt[XX[1+i,j]^2+YY[1+i,j]^2]])-((-XX[i,j]+XX[i,1+j]) XX[1+i,j])/d^2-((-YY[i,j]+YY[i,1+j]) YY[1+i,j])/d^2))/d^2-
((-YY[i,j]+YY[i,1+j]) (1/2 (-F[Sqrt[XX[i,1+j]^2+YY[i,1+j]^2]]-F[Sqrt[XX[1+i,j]^2+YY[1+i,j]^2]])-(XX[i,1+j] (-XX[i,j]+XX[1+i,j]))/d^2-(YY[i,1+j] (-YY[i,j]+YY[1+i,j]))/d^2))/d^2)/
(-(((-XX[i,j]+XX[1+i,j]) (-YY[i,j]+YY[i,1+j]))/d^4)+((-XX[i,j]+XX[i,1+j]) (-YY[i,j]+YY[1+i,j]))/d^4)), Null];
YY[i+1,j+1]=
	If[d^2 (i+1)(j+1)<max,
	-((d^2 F[Sqrt[XX[i,1+j]^2+YY[i,1+j]^2]] XX[i,1+j]+d^2 F[Sqrt[XX[1+i,j]^2+YY[1+i,j]^2]] XX[i,1+j]+2 XX[i,j]^2 XX[i,1+j]-2 XX[i,j] XX[i,1+j]^2-d^2 F[Sqrt[XX[i,1+j]^2+YY[i,1+j]^2]] XX[1+i,j]-
d^2 F[Sqrt[XX[1+i,j]^2+YY[1+i,j]^2]] XX[1+i,j]-2 XX[i,j]^2 XX[1+i,j]+2 XX[i,1+j]^2 XX[1+i,j]+2 XX[i,j] XX[1+i,j]^2-2 XX[i,1+j] XX[1+i,j]^2+2 XX[i,j] YY[i,j] YY[i,1+j]-2 XX[i,1+j] YY[i,j] YY[i,1+j]-
2 XX[i,j] YY[i,j] YY[1+i,j]+2 XX[1+i,j] YY[i,j] YY[1+i,j]+2 XX[i,1+j] YY[i,1+j] YY[1+i,j]-2 XX[1+i,j] YY[i,1+j] YY[1+i,j])
/(2 (XX[i,1+j] YY[i,j]-XX[1+i,j] YY[i,j]-XX[i,j] YY[i,1+j]+XX[1+i,j] YY[i,1+j]+XX[i,j] YY[1+i,j]-XX[i,1+j] YY[1+i,j]))), Null];
      , {j, 0, M - 1}]
    , {i, 0, M - 1}];)

step = 1.86159/200;
iter = 200;
prog[step, iter, 1/16 (4 + #1^2)^2 &, 2 Tan[#1/2] &, 1.86159];

X=Interpolation[Evaluate[Flatten[Table[{{step i,step j},XX[i,j]},{i,0,iter},{j,0,iter}],1]]];
Y=Interpolation[Evaluate[Flatten[Table[{{step i,step j},YY[i,j]},{i,0,iter},{j,0,iter}],1]]];

x[u_, v_] := X[u, v]/(1 + 0.25 (X[u, v]^2 + Y[u, v]^2))
y[u_, v_] := Y[u, v]/(1 + 0.25 (X[u, v]^2 + Y[u, v]^2))
z[u_, v_] := (4 - (X[u, v]^2 + Y[u, v]^2))/(4 + (X[u, v]^2 + Y[u, v]^2))
r[u_, v_] := {x[u, v], y[u, v], z[u, v]}

dXdu = Derivative[1, 0][X];
dXdv = Derivative[0, 1][X];
dYdu = Derivative[1, 0][Y];
dYdv = Derivative[0, 1][Y];

gu[u_?NumericQ, v_?NumericQ] := gu[u, v] = (Y[u,v]dXdv[u,v]-X[u,v]dYdv[u,v])/(1+1/4 (X[u,v]^2+Y[u,v]^2))^2
gv[u_?NumericQ, v_?NumericQ] := gv[u, v] = (X[u,v]dYdu[u,v]-Y[u,v]dXdu[u,v])/(1+1/4 (X[u,v]^2+Y[u,v]^2))^2


taugu[L_] := f /. NDSolve[{f'[u] == gu[u, L], f[L] == 0}, f, {u, 0, L}][[1]]
taugv[L_] := f /. NDSolve[{f'[v] == gv[L, v], f[L] == 0}, f, {v, 0, L}][[1]]


(*Solve for \[CapitalGamma], \[CapitalTheta]*)
\[CapitalGamma]small[s_]=\[Pi]/2-s+s^3/18-7s^5/1800;
sphereProblem[e_]:={\[CapitalGamma]'[s]==\[Theta][s],\[Theta]'[s]==(-Sin[\[CapitalGamma][s]]-\[Theta][s])/s,\[CapitalGamma][e]==\[CapitalGamma]small[e],\[Theta][e]==D[\[CapitalGamma]small[s],s]/.s->e}
sphereSolve[e_,L_]:=NDSolve[Evaluate[sphereProblem[e]],{\[CapitalGamma],\[Theta]},Evaluate[{s,e,L}]];
Plot[Evaluate[{\[CapitalGamma][s]/.sphereSolve[0.001,2][[1]],\[CapitalGamma][s]/.sphereSolve[0.0001,2][[1]]}],{s,0.001,2}, PlotLegends->{"e=0.001", "e=0.0001"}]
Plot[Evaluate[{\[CapitalGamma][s]/.sphereSolve[0.0001,2][[1]],\[Theta][s]/.sphereSolve[0.0001,2][[1]]}],{s,0.0001,2}, PlotLegends -> {"\[CapitalGamma]", "\[Theta]"}]

e=0.0001;
sim\[CapitalGamma]=\[CapitalGamma]/.sphereSolve[e,2][[1]];
sim\[Theta]=\[Theta]/.sphereSolve[e,2][[1]];
d\[CapitalGamma]small[s_] = D[\[CapitalGamma]small[s], s];

\[CapitalGamma][s_?NumericQ] := If[s < e, \[CapitalGamma]small[s], sim\[CapitalGamma][s]];
\[Theta][s_?NumericQ] := If[s < e, d\[CapitalGamma]small[s], sim\[Theta][s]];

pu[u_?NumericQ, v_?NumericQ] := pu[u, v] = -((v \[Theta][u v])/Sin[\[CapitalGamma][u v]]);
pv[u_?NumericQ, v_?NumericQ] := pv[u, v] = -((u \[Theta][u v])/Sin[\[CapitalGamma][u v]]);

(*Calculate \[Tau]1, \[Tau]2*)
algo[L_, n_, a_, b_] := Module[{j, k, t1, t2, val},
  t1 = Table[0., {j, 0, n}, {k, 0, n}];
  t2 = Table[0., {j, 0, n}, {k, 0, n}];
  
  Do[
    val = N[(L j)/n];
    t1[[n + 1, j + 1]] = a Sin[\[CapitalGamma][L val]]^2;
    t2[[j + 1, n + 1]] = b Sin[\[CapitalGamma][L val]]^2;
    t1[[j + 1, n + 1]] = b/2 (L^2 \[Theta][L^2]^2 - val^2 \[Theta][L val]^2) + a Sin[\[CapitalGamma][L^2]]^2 + taugu[L][val];
    t2[[n + 1, j + 1]] = a/2 (L^2 \[Theta][L^2]^2 - val^2 \[Theta][L val]^2) + b Sin[\[CapitalGamma][L^2]]^2 + taugv[L][val];
  , {j, 0, n}];

  Do[
    Do[
    iterations = iterations + 1;
      
    uVal = L/(2 n) + (j L)/n;
    vVal = L/(2 n) + (k L)/n;
    
    denom = -4 n^2 + L^2 pu[uVal, vVal] pv[uVal, vVal];
    (*Second-order scheme*)
    
    t1[[j + 1, k + 1]] = -((-8 L n gu[uVal, vVal] - 
        4 n^2 t1[[j + 1, k + 2]] + 
        4 n^2 t1[[j + 2, k + 1]] + 
        4 n^2 t1[[j + 2, k + 2]] - 
        4 L^2 gv[uVal, vVal] pv[uVal, vVal] + 
        4 L n t2[[j + 1, k + 2]] pv[uVal, vVal] + 
        4 L n t2[[j + 2, k + 2]] pv[uVal, vVal] + 
        L^2 t1[[j + 1, k + 2]] pu[uVal, vVal] pv[uVal, vVal] + 
        L^2 t1[[j + 2, k + 1]] pu[uVal, vVal] pv[uVal, vVal] + 
        L^2 t1[[j + 2, k + 2]] pu[uVal, vVal] pv[uVal, vVal])/denom);
    
    t2[[j + 1, k + 1]] = -((-8 L n gv[uVal, vVal] + 
        4 n^2 t2[[j + 1, k + 2]] - 
        4 n^2 t2[[j + 2, k + 1]] + 
        4 n^2 t2[[j + 2, k + 2]] - 
        4 L^2 gu[uVal, vVal] pu[uVal, vVal] + 
        4 L n t1[[j + 2, k + 1]] pu[uVal, vVal] + 
        4 L n t1[[j + 2, k + 2]] pu[uVal, vVal] + 
        L^2 t2[[j + 1, k + 2]] pu[uVal, vVal] pv[uVal, vVal] + 
        L^2 t2[[j + 2, k + 1]] pu[uVal, vVal] pv[uVal, vVal] + 
        L^2 t2[[j + 2, k + 2]] pu[uVal, vVal] pv[uVal, vVal])/denom);
      
      If[Mod[iterations, 1000] == 0, Print["Iterations=", iterations]];
    , {k, n - 1, 0, -1}];
  , {j, n - 1, 0, -1}];
  
  {t1, t2}
];

sol = algo[L, n, a, b];
t1 = sol[[1]];
t2 = sol[[2]];

(*Convert \[Tau] to tensions*)
tension[T_] := Table[
  Module[{u, v, val},
    u = d*(i - 1);
    v = d*(j - 1);
    val = T[[i, j]] / Sin[\[CapitalGamma][u v]]^2;
    val
  ],
  {i, Length[T]}, {j, Length[T[[1]]]}
];

T11=tension[t1];
T22=tension[t2];

T11Coords=T11;
T22Coords=T22;
T11Coords=Reverse /@ Reverse[Transpose[T11]]//(Reverse /@ # &);
T22Coords=Reverse /@ Reverse[Transpose[T22]]//(Reverse /@ # &);

Print["Tension T1 at origin=", T11Coords[[n+1,1]]];
Print["Tension T2 at origin=", T22Coords[[n+1,1]]];


tau1u[L_,v_]:=gu[L,v]-(L \[Theta][L v])/Sin[\[CapitalGamma][L v]] taugv[L][v]

plota = Plot[Evaluate[tau1u[0.5, v]], {v, 0, 0.5}, PlotStyle -> Black];
plotb = Plot[Evaluate[tau1u[1.0, v]], {v, 0, 1.0}, PlotStyle -> Green];
plotc = Plot[Evaluate[tau1u[1.2, v]], {v, 0, 1.2}, PlotStyle -> Red];
plotd = Plot[Evaluate[tau1u[1.3, v]], {v, 0, 1.3}, PlotStyle -> Blue];

Legended[
  Show[
    plota, plotb, plotc, plotd,
    PlotRange -> All,
    ImageSize -> 400,
    Frame -> True,
    GridLines -> Automatic,
    GridLinesStyle -> Directive[LightGray, Thin],
    FrameLabel -> {
      Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style["\[Tau]\:2081\:1d64(L,v)", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
    },
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
  ],
  Placed[
    LineLegend[
      {Black, Green, Red, Blue},
      {"L = 0.5", "L = 1", "L = 1.2", "L = 1.3"},
      LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
      LegendMarkerSize -> {25, 12}
    ],{0.8,0.25}
  ]
]

plote = Plot[Evaluate[taugu[0.5][v]], {v, 0, 0.5}, PlotStyle -> Black];
plotf = Plot[Evaluate[taugu[1.0][v]], {v, 0, 1.0}, PlotStyle -> Green];
plotg = Plot[Evaluate[taugu[1.2][v]], {v, 0, 1.2}, PlotStyle -> Red];
ploth = Plot[Evaluate[taugu[1.3][v]], {v, 0, 1.3}, PlotStyle -> Blue];

Legended[
  Show[
    plote, plotf, plotg, ploth,
    PlotRange -> All,
    ImageSize -> 400,
    Frame -> True,
    GridLines -> Automatic,
    GridLinesStyle -> Directive[LightGray, Thin],
    FrameLabel -> {
      Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
	  Style[Row[{Subscript[\[Tau], 1], "(", "u", ", ", "L", ")"}],FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]},
    LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
  ],
  Placed[
    LineLegend[
      {Black, Green, Red, Blue},
      {"L = 0.5", "L = 1", "L = 1.2", "L = 1.3"},
      LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
      LegendMarkerSize -> {25, 12}
    ],{0.8,0.7}
  ]
]

ru[u_,v_]=D[r[u,v],u];
rv[u_,v_]=D[r[u,v],v];

\[Gamma]func[u_, v_] := ArcCos[(ru[u, v] . rv[u, v])]

data = Table[
   Evaluate[N[\[Gamma]func[u, v]*180/\[Pi]]],
   {u, 0, L, L/n},
   {v, 0, L, L/n}
];

min\[Gamma]Val = Min[data];
max\[Gamma]Val = Max[data];

posMin = Position[data, min\[Gamma]Val];
posMax = Position[data, max\[Gamma]Val];


DensityPlot[
  \[Gamma]func[u, v]*180/\[Pi],
  {u, 0, L}, {v, 0, L},
  PlotLegends -> BarLegend[
    {"TemperatureMap", {0,90}},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> "\[Gamma]",
    LegendMarkerSize -> {15, 225}
  ],
  FrameLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", 14],
    Style["v", FontFamily -> "Latin Modern Roman", 14]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  ImageSize->400,
  ColorFunction -> "TemperatureMap",
  PlotRange -> All
]
   
   
min\[Gamma][L_?NumericQ] := Module[{grid, vals},
  grid = Flatten[Table[{u,v}, {u,0,L,L/n}, {v,0,L,L/n}],1]; 
  vals = \[Gamma]func @@@ grid;
  Min[vals]*180/\[Pi]
]

Ls = Range[0.15, 1.35, 0.2];

minVals = Table[min\[Gamma][L], {L, Ls}];


Legended[
  Show[
    {
      ListLinePlot[
        Transpose[{Ls, minVals}],
        PlotStyle -> Blue
      ],
      Plot[
        \[CapitalGamma][L^2]*180/\[Pi],
        {L, Min[Ls], Max[Ls]},
        PlotStyle -> {Red, Dashed}
      ]
    },
    Frame -> True,
    FrameLabel -> {
      Style["L", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
      Style["Minimum \[Gamma]", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
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
    {0.25, 0.25}
  ]
]


R=ConstantArray[0, Dimensions[T11]];
Do[Do[valU=N[u*d];
valV=N[v*d];
R[[u+1,v+1]]=Evaluate[N[T11[[u+1,v+1]]+T22[[u+1,v+1]]+z[valU,valV]/Sin[\[CapitalGamma][valU valV]]]];
,{v,0,n,1}],{u,0,n,1}];

ListDensityPlot[
  R,
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  DataRange->{{0,L},{0,L}},
  PlotRange -> All,
  ImageSize -> 400,
  FrameLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  PlotLegends -> BarLegend[
    {"TemperatureMap", MinMax[R]},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> "R",
    LegendMarkerSize -> {15, 225}
  ]
]


RCoords=Reverse[R];

{rmin, rmax} = MinMax[R];
posMin = Position[R, rmin];
posMax = Position[R, rmax];

coordsMin = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMin);
coordsMax = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMax);

Print["Min value: ", rmin, " at spatial coords: ", coordsMin];
Print["Max value: ", rmax, " at spatial coords: ", coordsMax];

plot1=Flatten[Table[{d*j, d*k,T11[[j+1,k+1]]},{j,0,n},{k,0,n}],1];
pl1=ListPlot3D[plot1,TicksStyle->Directive[FontFamily->"Latin Modern Roman" ],AxesLabel->Table[Style[q,FontFamily->"Latin Modern Roman",FontSize->14],{q,{u,v,T1}}],PlotRange->All, ColorFunction->"TemperatureMap"]

plot2=Flatten[Table[{d*j, d*k,T22[[j+1,k+1]]},{j,0,n},{k,0,n}],1];
pl2=ListPlot3D[plot2,TicksStyle->Directive[FontFamily->"Latin Modern Roman" ],AxesLabel->Table[Style[q,FontFamily->"Latin Modern Roman",FontSize->14],{q,{u,v,T2}}],PlotRange->All, ColorFunction->"TemperatureMap"]


tensionData2DT1=Flatten[Table[{(i-1)d, (j-1)d, T11[[i,j]]}, {i,1,n+1}, {j,1,n+1}], 1];

tensionInterpT1=Interpolation[tensionData2DT1];

Print["Min/Max of tension T1=", MinMax[tensionData2DT1[[All,3]]]];

tensionData2DT2 = Flatten[Table[{(i-1)d, (j-1)d, T22[[i,j]]},{i,1,n+1}, {j,1,n+1}],1];

tensionInterpT2=Interpolation[tensionData2DT2];

Print["Min/Max of tension T2=", MinMax[tensionData2DT2[[All,3]]]];

(*2D - T1, T2*)
ListDensityPlot[
  tensionData2DT1,
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange -> All,
  Frame -> True,
  FrameLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  PlotLegends -> BarLegend[
    {"TemperatureMap", MinMax[tensionData2DT1[[All, 3]]]},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 1],
    LegendMarkerSize -> {15, 225}
  ],
  ImageSize -> 400,
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
]


ListDensityPlot[
  tensionData2DT2,
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange -> All,
  Frame -> True,
  FrameLabel -> {
    Style["u", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["v", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  PlotLegends -> BarLegend[
    {"TemperatureMap", MinMax[tensionData2DT2[[All, 3]]]},
    LabelStyle -> Directive[FontSize -> 14, FontFamily -> "Latin Modern Roman", Black],
    LegendLabel -> Subscript["T", 2],
    LegendMarkerSize -> {15, 225}
  ],
  ImageSize -> 400,
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black}
]

(*3D tension plot*)
(*T1*)
data3DT1 = Flatten[
  Table[{(i-1)d, (j-1)d, T11[[i, j]]},
    {i, 1, n + 1}, {j, 1, n + 1}
  ],
  1
];

data3DT2 = Flatten[
  Table[{(i-1)d, (j-1)d, T22[[i, j]]},
    {i, 1, n + 1}, {j, 1, n + 1}
  ],
  1
];

tensionInterpT1 = Interpolation[
  data3DT1[[All, {1, 2, 3}]] /. {u_, v_, tension_} :> {{u, v}, tension}
];

tensionInterpT2 = Interpolation[
  data3DT2[[All, {1, 2, 3}]] /. {u_, v_, tension_} :> {{u, v}, tension}
];

minTensionT1 = Min[data3DT1[[All, 3]]];
maxTensionT1 = Max[data3DT1[[All, 3]]];
minTensionT2 = Min[data3DT2[[All, 3]]];
maxTensionT2 = Max[data3DT2[[All, 3]]];

colourFuncT1=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT1[x, y], {minTensionT1, maxTensionT1}]]
];

colourFuncT2=Function[{x, y, z},
  ColorData["TemperatureMap"][Rescale[tensionInterpT2[x, y], {minTensionT2, maxTensionT2}]]
];


sphereAll = ParametricPlot3D[
   0.98 {Sin[\[Theta]] Cos[\[Phi]], Sin[\[Theta]] Sin[\[Phi]], Cos[\[Theta]]}, 
   {\[Theta], 0, \[Pi]}, {\[Phi], 0, 2 \[Pi]},
   RegionFunction -> Function[{x, y, z, \[Theta], \[Phi]}, x^2 + y^2 <= 1], 
   PlotStyle -> Directive[LightGray, Opacity[0.6]], 
   Mesh -> None
];

fibreNum=L/5;

tensionPlotT1 = ParametricPlot3D[
   r[u, v],
   {u, 0, L}, {v, 0, L},
   PlotPoints -> 50,
   MaxRecursion -> 1,
   ColorFunction -> colourFuncT1,
   ColorFunctionScaling -> False,
   Mesh -> None,
   ImageSize->400,
   Lighting -> "Neutral"
];

(*3D - T1, T2*)
rotationTransform = RotationTransform[-Pi/2, {0, 0, 1}];

transformGraphics[g_Graphics3D] := 
  g /. Graphics3D[prims_, opts___] :> 
    Graphics3D[GeometricTransformation[prims, rotationTransform], opts];

Legended[
 Show[
  {
   transformGraphics[sphereAll],
   ParametricPlot3D[
     Evaluate[r[u, v]],
     {u, 0, L}, {v, 0, L},
     PlotPoints -> 50,
     MaxRecursion -> 1,
     ColorFunction -> colourFuncT1,
     ColorFunctionScaling -> False,
     Mesh -> None,
     Lighting -> "Neutral"
   ] /. Graphics3D[prims_, opts___] :> 
        Graphics3D[GeometricTransformation[prims, rotationTransform], opts],

   Table[
     transformGraphics[
       ParametricPlot3D[
         Evaluate[r[u, v]], {v, 0, L},
         PlotStyle -> {Thickness[0.0025], Darker[Black]},
         PlotRange -> All
       ]
     ],
     {u, 0, L, L/5}
   ],
   
   Table[
     transformGraphics[
       ParametricPlot3D[
         Evaluate[r[v, u]], {v, 0, L},
         PlotStyle -> {Thickness[0.0025], Darker[Black]},
         PlotRange -> All
       ]
     ],
     {u, 0, L, L/5}
   ]
  },
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


Legended[
 Show[
  {
   transformGraphics[sphereAll],
   ParametricPlot3D[
     Evaluate[r[u, v]],
     {u, 0, L}, {v, 0, L},
     PlotPoints -> 50,
     MaxRecursion -> 1,
     ColorFunction -> colourFuncT2,
     ColorFunctionScaling -> False,
     Mesh -> None,
     Lighting -> "Neutral"
   ] /. Graphics3D[prims_, opts___] :> 
        Graphics3D[GeometricTransformation[prims, rotationTransform], opts],

   Table[
     transformGraphics[
       ParametricPlot3D[
         Evaluate[r[u, v]], {v, 0, L},
         PlotStyle -> {Thickness[0.0025], Darker[Black]},
         PlotRange -> All
       ]
     ],
     {u, 0, L, L/5}
   ],
   
   Table[
     transformGraphics[
       ParametricPlot3D[
         Evaluate[r[v, u]], {v, 0, L},
         PlotStyle -> {Thickness[0.0025], Darker[Black]},
         PlotRange -> All
       ]
     ],
     {u, 0, L, L/5}
   ]
  },
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



