(* ::Package:: *)

ClearAll["Global`*"]
Remove["Global`*"]

L=1.2; (*Max L=1.36*)
n=40;
d=L/n;
a=1;
b=1;

iterations=0;

prog[d_,M_,F_,g_, max_]:=(Do[XX[0,j]=0;
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

step=1.86159/100;
iter=100;
prog[step,iter,1/16 (4+#^2)^2&,2 Tan[#/2]&,1.86159]

Do[XX[i,j]=Sign[i]XX[Abs[i],Abs[j]];YY[i,j]=Sign[j]YY[Abs[i],Abs[j]];,{i,-1,iter},{j,-1,iter}]

X=Interpolation[Evaluate[Flatten[Table[{{step i,step j},XX[i,j]},{i,0,iter},{j,0,iter}],1]]];
Y=Interpolation[Evaluate[Flatten[Table[{{step i,step j},YY[i,j]},{i,0,iter},{j,0,iter}],1]]];

x[u_,v_]:=X[u,v]/(1+0.25(X[u,v]^2+Y[u,v]^2))
y[u_,v_]:=Y[u,v]/(1+0.25(X[u,v]^2+Y[u,v]^2))
z[u_,v_]:=(4-(X[u,v]^2+Y[u,v]^2))/(4+(X[u,v]^2+Y[u,v]^2))
r[u_,v_]:={x[u,v],y[u,v],z[u,v]}

\[CapitalGamma]small[s_]=\[Pi]/2-s+s^3/18-7s^5/1800;
sphereProblem[e_]:={\[CapitalGamma]'[s]==\[CapitalGamma]1[s],\[CapitalGamma]1'[s]==(-Sin[\[CapitalGamma][s]]-\[CapitalGamma]1[s])/s,\[CapitalGamma][e]==\[CapitalGamma]small[e],\[CapitalGamma]1[e]==D[\[CapitalGamma]small[s],s]/.s->e}
sphereSolve[e_,L_]:=NDSolve[Evaluate[sphereProblem[e]],{\[CapitalGamma],\[CapitalGamma]1},Evaluate[{s,e,L}]];

e=0.0001;
sol=sphereSolve[e, 2];
\[CapitalGamma]Sol=\[CapitalGamma]/.sol[[1]];
\[CapitalGamma]Func[s_?NumericQ]:=Piecewise[{{\[CapitalGamma]small[s], s <= e}, {\[CapitalGamma]Sol[s], s > e}}];

\[Gamma][s_?NumericQ]:=\[CapitalGamma]Func[s];
\[Phi]s[s_?NumericQ]:=ArcTanh[Cos[\[CapitalGamma]Func[s]]];

\[Phi][u_?NumericQ, v_?NumericQ]:=Module[{s=u v}, \[Phi]s[s]];

\[Phi]u[u_?NumericQ, v_?NumericQ]:=Module[{s=u v}, v*\[Phi]s'[s]];
\[Phi]v[u_?NumericQ, v_?NumericQ]:=Module[{s=u v}, u*\[Phi]s'[s]];


sechsquared\[Phi][u_?NumericQ, v_?NumericQ]:=Sech[\[Phi][u,v]]^2;

tau1u[u_?NumericQ]:=-sechsquared\[Phi][u, L]*\[Phi]v[u, L];
tau2v[v_?NumericQ]:=-sechsquared\[Phi][L, v]*\[Phi]u[L, v];

(*T12=Solve[{(T1[u+d,v]-T1[u,v])/d+T2[u,v]pv[u,v],(T2[u,v+d]-T2[u,v])/d+T1[u,v]pu[u,v]}==0,{T1[u,v],T2[u,v]}]/.d->L/n//Simplify;*) (*First-order scheme*)
T12=Solve[{((T1[u+d,v]-T1[u,v])+(T1[u+d,v+d]-T1[u,v+d]))/(2d)+((T2[u,v]+T2[u+d,v]+T2[u,v+d]+T2[u+d,v+d])pv[u+d/2,v+d/2])/4,
((T2[u,v+d]-T2[u,v])+(T2[u+d,v+d]-T2[u+d,v]))/(2d)+((T1[u,v]+T1[u+d,v]+T1[u,v+d]+T1[u+d,v+d])pu[u+d/2,v+d/2])/4}==0,{T1[u,v],T2[u,v]}]/.d->L/n//Simplify;

T12fd={T1[u,v],T2[u,v]}/.T12[[1]];

t12fd = T12fd/.{
  T1[u_,v_] :> t1[[u/d + 1, v/d + 1]],
  T2[u_,v_] :> t2[[u/d + 1, v/d + 1]]
};
t12fd = t12fd/.{u->j d, v->k d};

T12jkSub[j_,k_]=t12fd/.{j->N[j], k->N[k], pu[u_,v_]->\[Phi]u[u,v],pv[u_,v_]->\[Phi]v[u,v]}//Simplify;

t1=Table[0,{j,0,n},{k,0,n}];
t2=Table[0,{j,0,n},{k,0,n}];

Do[val=N[L*j/n];
t1[[n+1,j+1]]=Evaluate[N[sechsquared\[Phi][L, val]]*a];
t2[[j+1,n+1]]=Evaluate[N[sechsquared\[Phi][L, val]]*b];
t1[[j+1,n+1]]=Evaluate[N[sechsquared\[Phi][L,L]*a-b*(NIntegrate[tau1u[u], {u, val, L}])]];
t2[[n+1,j+1]]=Evaluate[N[sechsquared\[Phi][L,L]*b-a*(NIntegrate[tau2v[v], {v, val, L}])]];
,{j,0,n}];


Do[Do[
iterations=iterations+1;

t1[[j+1,k+1]]=Evaluate[N[T12jkSub[j,k][[1]]]];
t2[[j+1,k+1]]=Evaluate[N[T12jkSub[j,k][[2]]]];

If[Mod[iterations, 10000]==0, Print["Iterations=", iterations]];
,{k,n-1,0,-1}],{j,n-1,0,-1}];


tension[T_]:=Table[
  Module[{u, v, val},
    u=d*(j-1);
    v=d*(i-1);
    val=T[[i,j]]/sechsquared\[Phi][u,v];
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

R=Reverse[T11Coords]+Reverse[T22Coords];


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
pl1=ListPlot3D[plot1,TicksStyle->Directive[FontFamily->"Latin Modern Roman" ],AxesLabel->Table[Style[q,FontFamily->"Latin Modern Roman",FontSize->14],{q,{u,v,T1}}],PlotRange->All]


tensionData2DT1=Flatten[Table[{(i-1)d, (j-1)d, T11[[i,j]]}, {i,1,n+1}, {j,1,n+1}], 1];

tensionInterpT1=Interpolation[tensionData2DT1];

Print["Min/Max of tension T1=", MinMax[tensionData2DT1[[All,3]]]];

tensionData2DT2 = Flatten[Table[{(i-1)d, (j-1)d, T22[[i,j]]},{i,1,n+1}, {j,1,n+1}],1];

tensionInterpT2=Interpolation[tensionData2DT2];

Print["Min/Max of tension T2=", MinMax[tensionData2DT2[[All,3]]]];


(*2D tension plot*)
(*T1*)
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

(*T2*)
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

(*T1/T2 - One quadrant with sphere*)
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


(* ::Message:: *)
(*Part::pkspec1*)


(* ::Input:: *)
(**)
(**)
(**)
(**)
(**)
(**)
(**)
(**)
(**)
(**)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)


(* ::Message:: *)
(*Show::gcomb*)


(* ::Message:: *)
(*Show::gcomb*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*\[AliasDelimiter]*)


(* ::Print:: *)
(*SequenceForm["T1 Coords=", MatrixForm[CompressedData["*)
(*1:eJxF1Hs01ekeBvByYjuTIjVyGyFi6MZKYqqnknDQxXRzqVQTldiGKWIoSW6R*)
(*XHedSLlTdEJR41bGpXKpE5IudIS92ft327+9xcSxZs2a/V3rXc+fn/d91ne9*)
(*eke4LsfkZs2apfLX2fq4wCc4aAiW1k9WBoYPIVtlbV9y2hC2vnNmLR4NIaI8*)
(*/EYRMQRn/4N2fhbDWN566ol2wjDUvPon7ceHURv02kfn7Ah+P+trFqrKB/UV*)
(*y5e38MHrVNm89aYAwYHzTW5kjSKnNycmuWMME6brx80gwqw/h0RuQX6z+YoR*)
(*+Fst2r7WdgQ6Tovt9h8ZgWjqm31OV0fwOee3usbmmWz+subJN3zkhq6m17nx*)
(*YbPExjXhIR/p3NpSroEA3YE+AqUcARxM5llarx2FeHFIfcnAKNxrF77aUjwG*)
(*4cXyg2HpQnRYdp9WL5P5hS91N/dFCFBo5rEmgSfAor1lPSWlAiw4c/ba09cC*)
(*7Gn/ruTQpADmgYVTuqaj2JMV8pR/eBQJuazttVuj0DePGzw9Ogrj/a5VezeP*)
(*4WRYV1Jy3hii9kx5mWgJwWuvzfgjT4jMaxXfznUUweGj9lifCvG33+6tV5g6*)
(*OAZepJJFwZcxsNELfB9zhFDLqmczlwqRUhCVsmmdEMPjNgcOuQgxFKF4utRX*)
(*CDfv787XXBZCzrhiMO6eEApx7+49eyvEQGxfZNI8EYpLHwwHznj9kXdRliHC*)
(*mdzjsx0kIvxwOPC4wymZrwh9tT2OBLo5yRciDhJ4tsBjQaoXAebK5YeGgQTu*)
(*Dkbv3BREIK7v1ht6Ji8X93BNzxC4JHXNUw4g4LAhNuKSL4HE82Ue6icJ+JFx*)
(*mt0nCFyw/exnxiXwb6HerG/DCCTlrSwYTyewMyppYqJe5h/LeEsGd5N4XnFb*)
(*afoDCVt32xu6/SQ6w1I2Vr8nYW156IhTD4kjynVFRCuJnIPjCS3VJIbjjIpc*)
(*8kgoh0mXGSeSaJrrEqV6mkR5YfgiE3cSYl3u8YrNJCwVql/qmZCoktqfUlUj*)
(*Ma8Xzq4c8m+//L8i3z+mKRSFBcUe4NAIt7eRi5Gn8TGc4ZJfKPBFy6JaBRQG*)
(*DOU4azoosAY1dimlFGiLCf/30RRiT7X2nHGnYPf7mrY5phQUWlZ7ZktJxMS0*)
(*hVY8IaFu5ejWmkDiiql6U6QbCaN9d4tzTGT+/PCBQJEGg+3VDdo6ugxemnZs*)
(*dNNiULryp+e2CgxWm7++dlREY6Xq8ptlzTQczEyKstNozA/N1uR70FCa3sTS*)
(*WjQMp9Q3x76m4NRU3RwdQ2Eo/+e+Q1YUwng1Sk0jJCZmG20K45EgEjV6nP8l*)
(*8zPM/Xr+aSRGvXHtG8XlYmRGNYZeNBBD18juBS0vRvlHg1fH+hl0Fl2cG1vG*)
(*gEuk9ij6MrD+lK1bN3PfNreCypgXNI5F9t/P49IYyJ6YXK9E47ZaxIW0XAql*)
(*LvOXBlhT+Nzebfywg4Thth1fHb1ITP85BHbYdk0oa7Ko71/WMvwdi/OmUW7D*)
(*C1nsTBbxlMfEaLmtnfVLlRgWZUXsjnAx7nM4FiFmYmw491ji84pBfJod03WC*)
(*gXNsE6fhCw2n6SVMUgQN19M12j7/mEmFPscVFygYbNewIqZJfMqPXZsaLnv/*)
(*rg3tAXdELLIH4gMCKBZfYy8zrp9ZPJNPPKz1G4tHG7W8VEJZBPlet9JYxcKK*)
(*2O0X1SvGekFqe5f/TF+tZfUNLIPcsqcHu/wZaHVFLjz/mUZDo+6Dd7tpTP/n*)
(*6IOxOgpK10fVVb+noBUf+UIjReYbPO/N88uVQFN/9gObfAl2bWu8nMqTIERp*)
(*74lKrgTyDylnM30Jzret+qGqkUW606WLuzxY7Bi8cZOY6Wf6QKdTiY8YH4r5*)
(*HNW3DEy7nzU0WjN4x2mqjE+nsZPWcV1GUnCR//FpkwOFil6jJ+U5Mt/S+HaC*)
(*41opOuSM5d0spbD4anPnjrEUP9ZxN3jPluLwzfnnmqolGFEI3ujpJEFlyf2A*)
(*pnYW05aTzXW2LIrbatrfVIqxjJ1XuVRfjFWPtH+1i2AQvS95ML+LRptnQGSJ*)
(*Hg36ntrJquMUeHM8GjTvy/wxXqTcVLoUWx5VmgRnSCH1tI4JipFCW39ykfJP*)
(*UmyXO5a5wVCKnYkrHD42S3CubOpcjb0Eciq8d94FLHad8diW9UWM6Lm+rn02*)
(*YvTSq1+pxDHIiNgbb9pJ4/u9j7oTNWiosYvnhntT2G3UxqaWy/x404VvJ/Ol*)
(*mH3rarBmgRSMu2PWOZ4UV6wVM9cHS/H007rwJVulGL8SnBczIYF3TP6pE9cl*)
(*uMp+3L9nqQR3f2Xtb6ex2J+bp+VBi7FGLuXT/6zF4Lsavvf6mYGOS3LxUR4N*)
(*c9L65pxKClem3hdUdct8Scib3A6GAftX1mfXcdyHZvpb4D8d+ZxB5mBayFAO*)
(*g8FO7iHPmf0SfFhc+9WMQUuHfLmET4M7KbflwTUaVXZvbzVvoWGvZ1WTNURB*)
(*0T6JeH2Jwi+6VR4CAwo6rYUejjP/kU9eRuM2T5n/fwbCEPs=*)
(*"]]]*)


(* ::Print:: *)
(*{(9 t1[[2+j,1+k]]+3 t2[[1+j,2+k]] \[Phi]v[j/3,k/3])/(9-\[Phi]u[j/3,k/3] \[Phi]v[j/3,k/3]),(9 t2[[1+j,2+k]]+3 t1[[2+j,1+k]] \[Phi]u[j/3,k/3])/(9-\[Phi]u[j/3,k/3] \[Phi]v[j/3,k/3])}*)


(* ::Message:: *)
(*TerminatedEvaluation["RecursionLimit"]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)
(**)
(**)


(* ::Message:: *)
(*Part::pkspec1*)


(* ::Message:: *)
(*General::stop*)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)


(* ::Print:: *)
(**)


(* ::Input:: *)
(**)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
(**)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)


(* ::Input:: *)
(**)
(**)


(* ::Input:: *)
(* *)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
(**)


(* ::Input:: *)
(**)


(* ::Print:: *)
(**)
(**)
(**)
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


(* ::Input:: *)
(**)


(* ::Message:: *)
(*$RecursionLimit::reclim*)


(* ::Input:: *)
(**)
