(* ::Package:: *)

ClearAll["Global`*"]
Remove["Global`*"]

L = 1;
n = 40;
d = L/n;
iterations = 0;

a = 0;
b = 0;

fuConst = 3;
fvConst = 1;

algo[L_,n_,a_,b_,fuConst_,fvConst_]:=Module[{d, t1=Table[0,{j,0,n},{k,0,n}],t2=Table[0,{j,0,n},{k,0,n}]},
d=L/n;

Clear[fu,fv,tabU,tabV];

eqZ[u_, v_] = - 1/2 (fuConst*fu[u]^2 + fvConst*fv[v]^2); (*-1/2 (fuConst*fu[u]^2+fv[v]^2) for paraboloid, 1/2 (fuConst*fu[u]^2 - fv[v]^2) for hyperbolic paraboloid*)
p = {fu[u], fv[v], eqZ[u, v]};

fu'[x_] := 1/Sqrt[1 + fuConst^2 * fu[x]^2];
fv'[x_] := 1/Sqrt[1 + fvConst^2 * fv[x]^2];

\[Phi]=ArcTanh[D[p,u] . D[p,v]];
\[Phi]uv={D[\[Phi],u],D[\[Phi],v]}//Simplify; 

sechsquared\[Phi]=Sech[\[Phi]]^2//Simplify;
sech2\[Phi][u_,v_]=Sech[\[Phi]]^2//Simplify;

tau1u=-sechsquared\[Phi]*\[Phi]uv[[2]]/.v->L; 
tau2v=-sechsquared\[Phi]*\[Phi]uv[[1]]/.u->L;

tau1L=Integrate[tau1u,u]; 
tau2L=Integrate[tau2v,v];

cos\[Gamma]=D[p,u] . D[p,v]//Simplify;
sin\[Gamma]=Sqrt[1-cos\[Gamma]^2]//Simplify;

RHS1=1/(sin\[Gamma])(D[p,u][[3]]-cos\[Gamma]*D[p,v][[3]]);
RHS2=1/(sin\[Gamma])(-cos\[Gamma]*D[p,u][[3]]+D[p,v][[3]]);

intRHS1L=RHS1/.v->L;
intRHS2L=RHS2/.u->L;
intRHS1uL=Integrate[intRHS1L,u]/.v->L//Simplify;
intRHS2Lv=Integrate[intRHS2L,v]/.u->L//Simplify;
intRHS1LL=intRHS1uL/.u->L;
intRHS2LL=intRHS2Lv/.v->L;

tau12uL=tau1L/.u->L;
tau12Lv=tau2L/.v->L;


tabU = Table[{1/2 (fu Sqrt[1 + fuConst^2 fu^2] + ArcSinh[fuConst fu]/fuConst), fu},
            {fu, -60, 60, 0.01}];
fiU = Interpolation[tabU];
fu[x_?NumericQ] := N[fiU[x]];

tabV = Table[{1/2 (fv Sqrt[1 + fvConst^2 fv^2] + ArcSinh[fvConst fv]/fvConst), fv}, 
            {fv, -60, 60, 0.01}];
fiV = Interpolation[tabV];
fv[x_?NumericQ] := N[fiV[x]];




RHS1=RHS1/.{u->u+d/2,v->v+d/2};
RHS2=RHS2/.{u->u+d/2,v->v+d/2};
T12=Solve[{((T1[u+d,v]-T1[u,v])+(T1[u+d,v+d]-T1[u,v+d]))/(2d)+((T2[u,v]+T2[u+d,v]+T2[u,v+d]+T2[u+d,v+d])pv[u+d/2,v+d/2])/4==RHS1,
((T2[u,v+d]-T2[u,v])+(T2[u+d,v+d]-T2[u+d,v]))/(2d)+((T1[u,v]+T1[u+d,v]+T1[u,v+d]+T1[u+d,v+d])pu[u+d/2,v+d/2])/4==RHS2},{T1[u,v],T2[u,v]}]//Simplify;
(*T12=Solve[{(T1[u+d,v]-T1[u,v])/d+T2[u,v]pv[u,v]==RHS1,(T2[u,v+d]-T2[u,v])/d+T1[u,v]pu[u,v]==RHS2},{T1[u,v],T2[u,v]}]//Simplify;*)


T12fd={T1[u,v],T2[u,v]}/.T12[[1]];

t12fd=T12fd/.{
  T1[u_,v_] :> t1dummy[[u/d + 1, v/d + 1]],
  T2[u_,v_] :> t2dummy[[u/d + 1, v/d + 1]]
};
t12fd=t12fd/.{u->j d, v->k d};

T12jk=t12fd/.d->L/n//Simplify;


T12jkSub[j_,k_]=T12jk/.{j->N[j], k->N[k], pu[u_,v_]->\[Phi]uv[[1]],pv[u_,v_]->\[Phi]uv[[2]]}//Simplify; 
tau1uL=(sechsquared\[Phi]/.{u->L,v->L})*a+b(tau1L-tau12uL)-intRHS1LL+intRHS1uL//Simplify; 
tau2Lv=(sechsquared\[Phi]/.{u->L,v->L})*b+a(tau2L-tau12Lv)-intRHS2LL+intRHS2Lv//Simplify;

tau2LvSub=tau2Lv/.L->N[L];
tau1uLSub=tau1uL/.L->N[L];

Do[val=N[j*d]; 
t1[[n+1,j+1]]=Evaluate[N[sechsquared\[Phi]/.{u->L, v->val}]*a];
t2[[n+1,j+1]]=Evaluate[N[tau2LvSub/.v->val]]; 
t1[[j+1,n+1]]=Evaluate[N[tau1uLSub/.u->val]]; 
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

sol=algo[L, n, a, b, fuConst, fvConst];
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

T11=tension[T11];
T22=tension[T22];
Print["Tension T1 at origin:", T11[[1,1]]];
Print["Tension T2 at origin:", T22[[1,1]]];

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



ListDensityPlot[
  R,
  DataRange -> {{0, L}, {0, L}},
  InterpolationOrder -> 0,
  ColorFunction -> "TemperatureMap",
  PlotRange->All,
  ImageSize -> 400,
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
]

RCoords=Reverse[R];

Print["Min/Max of reaction force R=", MinMax[R]];

{rmin, rmax} = MinMax[R];
Return[MinMax[R]];

posMin = Position[R, rmin];
posMax = Position[R, rmax];

Print["Min value: ", rmin, " at positions: ", posMin];
Print["Max value: ", rmax, " at positions: ", posMax];

coordsMin = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMin);
coordsMax = ({(#[[2]] - 1)*d, (#[[1]] - 1)*d} & /@ posMax);

Print["Min at spatial coords: ", coordsMin];
Print["Max at spatial coords: ", coordsMax];

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
   Module[{tens1, tens2, res, t1min, t1max, t2min, t2max},
     res = algo[1, n, 0, 0, fuConst, 1];
     tens1 = tension[res[[1]]];
     {t1min, t1max} = MinMax[tens1];
     tens2 = tension[res[[2]]];
     {t2min, t2max} = MinMax[tens2];
     Print["fu=", fuConst, " min=", t1max, " max=",t2max];
     {fuConst, t1min, t1max, t2min, t2max}
   ],
   {fuConst, 1, 6, 1}
];

xValues    = results[[All, 1]];
T1minVals  = results[[All, 2]];
T1maxVals  = results[[All, 3]];
T2minVals  = results[[All, 4]];
T2maxVals  = results[[All, 5]];

ListLinePlot[
  {
    Transpose[{xValues, T1maxVals}],
    Transpose[{xValues, T2maxVals}]
  },
  PlotStyle -> {
    {Blue, Thick},
    {Red, Thick}
  },
  PlotRange->All,
  PlotLegends -> Placed[{Style[Subscript["T", "1 min"], 14], Style[Subscript["T", "2 min"], 14]},{0.8,0.2}],
  Frame -> True,
  FrameLabel -> {
    Style["p", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black],
    Style["T", FontFamily -> "Latin Modern Roman", FontSize -> 14, Black]
  },
  LabelStyle -> {FontFamily -> "Latin Modern Roman", FontSize -> 12, Black},
  GridLines -> Automatic,
  GridLinesStyle -> Directive[LightGray, Thin],
  ImageSize -> 400
]


Plot[fiU[f], {f, -L, L}, PlotPoints -> 50, PlotLabel->Style["f", FontFamily -> "Latin Modern Roman", FontSize->14]]
Plot[fiV[f], {f, -L, L}, PlotPoints -> 50, PlotLabel->Style["f", FontFamily -> "Latin Modern Roman", FontSize->14]]

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
    {"TemperatureMap", {minTensionT1, maxTensionT1}},
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

surface = ParametricPlot3D[ (*surface for paraboloid*)
  {\[Rho] Cos[\[Theta]], \[Rho] Sin[\[Theta]], eqZ[\[Rho] Cos[\[Theta]], \[Rho] Sin[\[Theta]]] - offset},
  {\[Rho], 0, length}, {\[Theta], 0, 2 Pi},
  Mesh -> None,
  PlotStyle -> Opacity[0.6, LightGray],
  PlotRange -> All,
  BoxRatios -> {1, 1, 1}
];

(*surface = ParametricPlot3D[ (*surface for hyperbolic paraboloid*)
  {u, v, eqZ[u, v] - offset},
  {u, -L-0.2*L, L+0.2*L}, {v, -L-0.2*L, L+0.2*L},
  Mesh -> None,
  PlotStyle -> Opacity[0.6, LightGray],
  PlotRange -> All,
  BoxRatios -> {1, 1, 0.5}
];*)

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
       LegendLabel -> Subscript["T", 1],
       LegendMarkerSize -> {15, 225}
     ],
     Right
   ]
]



