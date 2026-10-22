#import "@preview/touying:0.7.3": *
#import themes.metropolis: *
#import "@preview/numbly:0.1.0": numbly
#import "@preview/curryst:0.3.0": *
#import "@preview/ctheorems:1.1.3" : *
#import "@preview/thmbox:0.3.0": *

#show: metropolis-theme.with(
  aspect-ratio : "16-9",
  config-info(
    title: [biunificationの正当性について],
    author: [Rei Tomori],
    date: datetime.today(),

  )
)
#set text(
  font: "Noto Serif JP",
  lang: "en",
  size: 17pt
)
#show regex("[\p{scx:Han}\p{scx:Hira}\p{scx:Kana}]"): set text(font: "IBM Plex Serif")
#set heading(numbering: numbly("{1}.", defualt: "1.1"))

#let bib = bytes(
  ```bib
      @book{dolan_algsub,
    author = {Dolan, Stephen},
    title = {Algebraic subtyping: Distinguished Dissertation 2017},
    year = {2017},
    isbn = {1780174152},
    publisher = {BCS Learning \& Development Ltd},
    }
    @article{dolan_mlsub_paper,
    author = {Dolan, Stephen and Mycroft, Alan},
    title = {Polymorphism, subtyping, and type inference in MLsub},
    year = {2017},
    issue_date = {January 2017},
    publisher = {Association for Computing Machinery},
    address = {New York, NY, USA},
    volume = {52},
    number = {1},
    issn = {0362-1340},
    url = {https://doi.org/10.1145/3093333.3009882},
    doi = {10.1145/3093333.3009882},
    abstract = {We present a type system combining subtyping and ML-style parametric polymorphism. Unlike previous work, our system supports type inference and has compact principal types. We demonstrate this system in the minimal language MLsub, which types a strict superset of core ML programs.  This is made possible by keeping a strict separation between the types used to describe inputs and those used to describe outputs, and extending the classical unification algorithm to handle subtyping constraints between these input and output types. Principal types are kept compact by type simplification, which exploits deep connections between subtyping and the algebra of regular languages. An implementation is available online.},
    journal = {SIGPLAN Not.},
    month = jan,
    pages = {60–72},
    numpages = {13},
    keywords = {Algebra, Polymorphism, Subtyping, Type Inference}
    }
```.text)



#show link: text.with(fill: blue)
#show: thmbox-init()
= Bisubstitutionの正当性について
== Bisubstitutionが制約を解くことの条件
#definition[
  typing scheme上の順序$attach(<=, tr: forall)$を，次のように定める:
  $
  [Delta_2]tau_2 attach(<=, tr: forall) [Delta_1] tau_1 <=> exists rho, Delta_1 <= rho(Delta_2), rho(tau_2) <= tau_1
  $
  ただし，$rho$は代入であってbisubstitutionではない．
]
#proposition[
  Bisubstitution $xi$が制約$C$を解くことの条件は，
  $
    forall rho models C, forall t^-, t^+, exists rho', rho'(xi t^+) <= rho(t^+) and rho(t^-) <= rho'(xi t^-)\
    forall rho' forall t^- , t^+, exists rho models C, rho(t^+) <= rho'(xi t^+) and rho'(xi t^-) <= rho(t^-)
  $
  ただし，$rho, rho'$は代入である(bisubstitutionとは限らない)
]
もとの論文#cite(<dolan_algsub>)における条件は，本来のもの(Prop.0.2)よりも強かった．
== Bisubstitutionが制約を解くことの条件(cont'd)
bisubstitution $xi$が安定，つまりidempotentかつ$forall alpha, xi(alpha^-) <= xi(alpha^+)$となるとき，Prop.0.2はより簡単なものに書き換えられた:
#proposition[
  安定なbisubstitution $xi$が制約$C$を解くことの条件は，
  $
    forall rho models C, forall t^-, t^+, exists rho', rho'(xi t^-) = rho(t^-), rho'(xi t^+) = rho(t^+)\
    forall t^-, t^+, exists rho models C, rho(t^+) <= xi t^+, xi t^- <= rho(t^-)
  $
]

とくにbaseの場合を考えれば十分なので，次が成り立つ:
#proposition[
  安定なbisubstitutionが制約$C$を解くことの条件は，$
                                     forall rho models C, forall alpha, exists rho', rho'(xi alpha^-) = rho(alpha) = rho'(xi alpha^+)\
                                     forall alpha, exists rho models C, xi alpha^- <= rho(alpha) <= xi alpha^+
                                   $
] <bisubst_solves2>

== Atomic Constraints
ある型$tau$が*constructed*であるとは，$tau$が基底型もしくは型構築子を適用して得られる型であることだった．
- つまり，$tau$は$mono(b o  o l)$または$tau_1 arrow tau_2$または${l_i : tau_1}$の形

atomicな制約は，次のように定義されていた:
#definition[
  制約$C$が*atomic*であるとは，$C$が$alpha <= t^-, alpha <= beta, t^+ <= alpha$の形であること．ただし$alpha, beta$は型変数，$tau^+, tau^-$はconstructed．
]

たとえば$alpha <= mono(b o o l), alpha <= beta arrow mono(b o o l)$はatomicだが$alpha <= mono(b o o l) inter.sq {l : alpha}$はatomicでない．

== Bisubstitutionが制約の解とならない例
- いま，atomicな制約$alpha <= t^-$に対し，bisubstitution $theta$を$theta = [mu beta^-. alpha inter.sq [beta slash alpha^-](t^-)slash alpha^-]$と定める．
  - この代入は安定である．(証明略)
  - $tau^-$に$alpha$が出現しない場合は$[alpha inter.sq t^- slash alpha^-]$に等しい．1回展開すれば得られる．
  - 他のケース($t^+<= alpha, alpha <= beta$)の場合は双対を取れば得られる．



#lemma[
  上のbisubstitution $theta$はatomicな制約$alpha <= t^-$を解く．
]
準備としていくつかの補題を示す必要があるので，それらを示すことにする．
== Atomicな制約の解となるBisubstitution
制約$alpha <= t^-$の解となるbisubstitution $theta$を$[mu ^- beta. alpha inter.sq [beta slash alpha^-](t^-)slash alpha^-]$と定める．最大後不動点の定義より，次が成り立つ:
#proposition[
  制約$alpha <= t^-$に対し，negativeな型の列$attach((t_n), br: n in bb(N))$を$t_0 = top, attach(t, br: n + 1) = alpha inter.sq [t_n slash alpha^-]t^-$と定める．$theta(alpha^-) = inter.sq.big_n t_n$．
] <bisubst_unroll>
== Atomicな制約の解となるBisubstitution(cont'd)
これは次に等しい:
#lemma[
  上記の$theta$に対し，$theta(alpha^-) = inter.sq.big_n t'_n$．ただし$t'_n = [alpha inter.sq t^- slash alpha^-]^n (alpha^-)$．(#cite(<dolan_algsub>), Lemma 45)
]

  - 各$t'_n$が減少列，i.e. $forall n, attach(t', br: n +1) inter.sq t'_n = attach(t', br: n + 1)$を$n$のinductionで示す．
    - $n = 0$のとき．$t'_1 inter.sq t'_0 = (alpha inter.sq t^-) inter.sq alpha^- = alpha inter.sq t^- = t'_1.$
    - 各$k$に対し，$attach(t', br: k + 1) inter.sq t'_k = attach(t', br: k + 1)$を仮定．このとき，$
  attach(t', br: k + 2) inter.sq attach(t', br: k + 1) = [alpha inter.sq t^- slash alpha^-](attach([alpha inter.sq t^-], tr: k+1)(alpha^-)) inter.sq [alpha inter.sq t^- slash alpha^-](attach([alpha inter.sq t^- slash alpha^-], tr:k)(alpha^-))\
  =[alpha inter.sq t^- slash alpha^-](attach(t', br: k + 1) inter.sq t'_k) = [alpha inter.sq t^- slash alpha^-]attach(t', br: k+1) = attach(t', br: k + 2).
  $となり$n = k + 1$でも成立．
- $forall n, alpha inter.sq [t'_n slash alpha^-]t^- = t'_n inter.sq [t'_n slash alpha^-]t^-$を示す． 
  - $n$を固定する．列$attach((t'_n), br: n in bb(N))$は上で見たように減少列なので，とくに$alpha = t'_0 >= t'_n$．$(alpha inter.sq [t'_n slash alpha^-]t^-) inter.sq (t'_n inter.sq [t'_n slash alpha^-]t^-) = t'_n inter.sq [t'_n slash alpha^-]t^-$なので$(>=)$の場合は成り立つ．
  - 逆の順序関係を示す．$
                    (alpha inter.sq [t'_n slash alpha^-]t^-) inter.sq t'_n equiv(alpha inter.sq [t'_n slash alpha^-]t^-) inter.sq (t'_n inter.sq [t'_n slash alpha^-]t^-) = alpha inter.sq [t'_n slash alpha^-]t^-
                  $
i.e. $alpha inter.sq [t'_n slash alpha^-]t^- <= t'_n$を示せばよい．$n$のinductionで示す．
- $n = 0$: $alpha inter.sq t^- <= alpha = t'_0$より従う．
- $n = k$: $alpha inter.sq [t'_k slash alpha^-]t^- <= t'_k$を仮定．このとき，bisubstitutionは束準同型，および(IH)より$alpha inter.sq [attach(t' , br: k + 1)slash alpha^-]t^- <= alpha inter.sq [t'_k slash alpha^-]t^- <= t'_k$．よって$alpha inter.sq [attach(t', br: k + 1)slash alpha^-]t^- <= t'_k inter.sq [attach(t', br: k + 1) slash alpha^-]t^- = attach(t', br: k + 1)$となり示される．
== Atomicな制約の解となるBisubstitution(cont'd)
ただし，最後の変形は次のようにして示される:
- 各$n$に対し，$
attach(t', br: n + 1) &= attach([alpha inter.sq t^- slash alpha^-], tr: n+ 1)(alpha^-) = [alpha inter.sq t^- slash alpha^-]^n (alpha inter.sq t^-) = [[alpha inter.sq t^- slash alpha^-]^n slash alpha^-](alpha inter.sq t^-)\
&= [t'_n slash alpha^-](alpha inter.sq t^-) =t'_n inter.sq [t'_n slash alpha^-]t^-
$
== Atomicな制約の解となるBisubstitution(cont'd)
#lemma("(Lemma 0.7の再掲)")[
  制約$alpha <= t^-$に対し，bisubstitution $theta$を$theta = [mu^- beta. alpha inter.sq [beta slash alpha^-]t^-slash alpha^-]$と定める．$theta$は$alpha <= t^-$を解く．
]
== Atomicな制約の解となるBisubstitution(cont'd)
@bisubst_solves2 の条件を充たすことを示す．ひとつめの条件について．$rho models alpha <= t^-, gamma$を任意に取る．
- case $gamma eq.not alpha$．$rho'$として$rho$を取れば，$rho(gamma^-) = rho(theta gamma) = rho(gamma) = rho(gamma^+)$から従う．
- case $gamma = alpha$．$theta$は$alpha$の正の出現には作用しないので，$rho(alpha) = rho'(alpha^+)$．したがって$rho = rho'$となる．あとは$rho(alpha^-) = rho(alpha)$を示せばよい．
  - @bisubst_unroll から，このbisubstitutionは単調減少する負の型の列$attach((t_n), br: n in bb(N))$の交わりでかける．$forall n in bb(N), rho(t_n)= rho(attach(inter.sq.big,b: k = 0, t: n)t_n) = rho(alpha)$を$n$のinductionで示す．
    - ここで$n = 0$の場合を考えると，$rho(top) = top = rho(alpha)$は成立しえない．$t^-$はconstructed，つまり基底型かレコードか矢印型であって，$rho(alpha)$は$rho(t^-)$のsubtypeなので$t^-$は$top$でなければならない．矛盾．
== Atomicな制約の解となるBisubstitution(cont'd)
  - Lemma 45の点列$(t'_n)$を用いる．
    - $n = 0$のとき．$t'_0 = alpha^-$より従う．
    - 各$n$に対して$rho(t'_n) = rho(alpha)$を仮定する．$rho(attach(t', br: n + 1)) =rho([alpha inter.sq t^-slash alpha^-]t'_n) = rho(alpha)$を示す．
      - (IH)より$rho(alpha) <= rho(t'_n)$．また$alpha$は$t$のcovariantな位置にのみ出現を許していたので，$rho(t^-) <= $
== 複数の制約に対するbisubstitutionの合成について
biunificationはatomicな制約になるまで不等式制約を分解し，制約解消のために生じたbisubstitutionたちを合成していた．
#lemma[
  制約$C_1, C_2$が与えられているとする．$xi_1, xi_2, xi_2 dot xi_1$が安定であり，$xi_1, x_2, xi_2 dot xi_1$がそれぞれ$C_1, C_2, xi_1(C_2)$を解くとする．このとき，$xi_2 dot xi_1$は$C_1, C_2$を解く．(#cite(<dolan_algsub>), Lemma 56)
]
= 型推論アルゴリズムへの影響
==
- このセクションでは，bisubstitutionが制約を解けないケースが決して人工的なものではなく，型推論アルゴリズムで出現しうるものであることを示す．
  - のちに見るように，制約がatomicな場合は解ける．解けないケースは複数の制約のinteractionの結果生じる．
== Bisubstitutionが制約の解になること: atomic case
#proposition("型推論アルゴリズムで出現するatomicな制約の解")[
任意の$Pi$，typing $[Delta]tau$，atomicな制約$c$に対して，$Pi$のもと$[Delta]tau,c$が型推論アルゴリズムで導出可能とする．$c$に対するbisubstitutionを$xi$とすると，$xi([Delta]tau)$のインスタンスは$c$のもとの$[Delta]tau$のインスタンスと一致する．
]
主要型アルゴリズムより，以下の2通りのみが可能．
- (App): $[Delta_1]beta, [Delta_2]tau_2, alpha$が存在し，$c = beta <= tau_2 arrow alpha$かつ$[Delta]tau = [Delta_1 inter.sq Delta_2]alpha$．
- (Proj) : $[Delta]beta$が存在し，$c = beta <= {l : alpha}$
= References
#bibliography(bib, style: "association-for-computing-machinery") 