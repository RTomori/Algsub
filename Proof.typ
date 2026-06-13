#import "@preview/js:0.1.3":*
#import "@preview/ctheorems:1.1.3" : *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import "@preview/thmbox:0.3.0": *
#show : js.with()
#show: thmbox-init()
#set text(
  font: "IBM Plex Serif",
  lang: "ja",
  size: 10pt
)

#maketitle(
  title: "On the Correctness of Biunification",
  authors: "Rei Tomori"
)
== Polar types
#definition()[
  polar typeを，次のように帰納的に定義する．$
                              t^+&colon.eq.double alpha|mono(b o o l)|bot|t^+ union.sq t^+|t^-arrow t^+|{l_i:tau_i^+}|mu alpha. t^+\
                              t^-&colon.eq.double alpha|mono(b o o l)|top|t^- inter.sq t^-|t^+ arrow t^-|{l_i:tau_i^-}|mu alpha. t^-
                            $
                        $t^+, t^-$をそれぞれ正の型，負の型という．]
論理定数(型変数)および論理定項(基底型)のpolarityはneutralである．ただし，再帰型には2つの条件がある:
#remark()[
  polarized typeにおいて，再帰型は以下の条件をみたす:
  - guardedness: $mu$-束縛された型変数は少なくとも一つの型コンストラクタ$(arrow, {})$の下にのみ出現する．
  - covariance: $mu$-束縛された型変数は偶数個の$arrow$の左にのみ出現する．
]

したがって，この構文においては，$mu alpha. alpha arrow mono(b o o l), mu alpha. alpha$は表現しえない．

= Questions to be solved
- $alpha <= t^-$の形の制約に対する再帰型のbisubstitutionが束縛変数の負の位置への代入に限ってよい理由
    - 型変数の各出現におけるpolarityは本体の型のそれに等しい．($because$ covariance conditionから，$mu$-boundな変数の各出現におけるpolarityは偶数回スイッチされるため)
    - したがって，制約が上限を与えるときは負の変数に代入されるのは負の型なので，このような制約で十分
  - lower boundの場合もその双対なので同じ．
- 再帰型で特徴付けられる代入は，展開列のlimit(colimit)として定められていた．列の最初は$top(bot)$であって，bisubstitutionが制約の解になる証明のbase caseを破綻させてしまう．これは再帰型の展開が実質的になされない場合に対応するが，落としてよいか?
    - よい．再帰型の展開が意味をなさない場合は$mu$束縛された変数が本体に出現しない，またはpolarityを無視した場合に限られる(証明せよ)
    - guardedness conditionに反する．本体における$mu$-boundな変数はかならず1つ以上のコンストラクタの下に出現しないといけないので，出現の余地はない．
    - occurs checkを通るか否かで分けられる．
- もし誤りがある場合は型注釈，もしくはelimination formに対する規則の場合に起こる．


#lemma()[
  $theta = [mu beta. alpha inter.sq [beta slash alpha^-](t^-)slash alpha^-]$とする．$theta(alpha^-) = inter.sq.big_n t_n$．ただし$t_1 = alpha inter.sq [top slash alpha^-]t^-, attach(t, br: n + 1)= alpha inter.sq [t_n slash alpha^-]t^-$．
]
これがsubtyping orderについての減少列であることは，$n$のinductionで分かる．$t^-$に$alpha$が負の位置に出現しない場合は一度のみ再帰型がunrollされた場合に相当し，自明．
- $alpha$が$t^-$に出現しない場合．$t_n = alpha inter.sq t^-$
- $alpha$が$t^-$の正の位置にのみ出現する場合．$t_1 = alpha inter.sq t^-, attach(t, br: n + 1) = alpha inter.sq [t_n slash alpha^-]t^- = alpha inter.sq t^-$で同様．

#proof[
  $n= 1$．$alpha inter.sq [alpha inter.sq [top slash alpha^-](t^-)slash alpha^-]t^- <= alpha inter.sq [top slash alpha^-]t^-$ i.e.$[alpha inter.sq [top slash alpha^-](t^-) slash alpha^-](t^-) <= [top slash alpha^-](t^-)$を示す．$t^-$が基底型の場合は自明なので，$t^-$が函数型かレコードの場合を考えればよい．
  - $t^-= {x_i : tau_i}$，ただしある$i$について$alpha$は$tau_i$の負の位置に出現する．
]


#theorem()[
  制約$alpha <= t^-$($t^-$ atomic)に対し，$xi = [mu beta. alpha inter.sq [beta slash alpha^-](t^-)slash alpha^-]$は制約を解く，つまり
  $
    forall [D^-]t^+, forall rho models alpha <= t^-, exists rho', rho'(xi[D^-]t^+) <= rho([D^-]t^+)\
    forall [D^-]t^+, forall rho', exists rho models alpha <= t^-, rho([D^-]t^+) <= rho'(xi[D^-]t^+)
  $
  これは次と同値:
  $
    forall t^-, t^+, forall rho models alpha <= t^-, exists rho', rho'(xi t^+) <= rho(t^+) and rho(t^-) <= rho'(xi t^-)\
    forall t^-, t^+, forall rho', exists rho models alpha <= t^-,rho t^+ <= rho' xi t^+, rho' xi t^- <= rho t^-
  $
]

  #proof[
 はじめの主張を示す．$rho models alpha <= t^-$を固定する．$t^+, t^-$に関するinductionで示す． 
 - case $t^+ = mono(b o o l)$．$t^-$のinductionで示す．
    - case $t^- = mono(b o o l), top$．恒等的な代入を取れば従う．
    - case $t^- = gamma eq.not alpha$．$rho' = rho$とすれば従う．
    - case $t^- = alpha$．$rho(alpha) <= rho'(xi alpha^-)$なる$rho'$が取れることを示す．unrollの列に関するinductionを回せばよい．
        - $n = 1$．$xi(alpha^-)  = alpha inter.sq t^-$．$rho(alpha) <= alpha inter.sq t^-$
    - (IH)任意の$t^+$に出現する負の型$tau^-$に対し，
]