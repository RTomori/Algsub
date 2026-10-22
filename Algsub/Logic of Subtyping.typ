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
  title: "A Logic Of Subtyping",
  authors: "Rei Tomori"
)
= Introduction
== 制限された線型含意としての部分型
ここでは二階の直観主義命題論理(i.e. System $bb(F)$)を論理的枠組みとして使おう．型上の帰結関係$sigma tack tau$は$sigma$が$tau$に含まれる(i.e. $sigma <= tau$)ことを意味するとする．部分型付けの論理は，通常の公理を持ち，$arrow$のdomainについて反変的でcodomainについて共変的でなければならない．すなわち，

#prooftree(
  rule(
    name:"ax",
    $sigma tack sigma$
  )
)
#prooftree(
  rule(
    name: $arrow$,
    $sigma' tack sigma$,$tau tack tau'$,
    $sigma arrow tau tack sigma' arrow tau'$
  )
)
つぎに，二階量化$forall$の論理的解釈を考える．$sigma$が型変数$X$の自由出現をもち，$sigma$のあるインスタンスから$tau$が導出できるとすると，より強く，$forall X.sigma tack tau$が導出できる．これが$forall text(左)$の規則だった．この意味論的解釈を部分型のPERモデルで与えることができる: ある型族のインスタンスが$tau$の部分型ならば，PERモデルでは，型族全体の交わりは$tau$の部分型となる．

#prooftree(
  rule(
    name: $forall L$,
    $[rho slash X]sigma tack tau$, $forall X.sigma tack tau$
  )
)
さらに，$sigma$の帰結が$tau$で，$sigma$が$X$の自由出現をもたないならば，$sigma$は$forall X.tau$を帰結する．意味論的には，$sigma <= tau$かつ$sigma$が$X$に依らないならば，$sigma$は$X$全体にわたり$tau$の交わりを取ったものの部分型．

#prooftree(
  rule(
    name: $forall R$,
    $sigma tack tau$, $sigma tack forall X.tau$
  )
)
型を他の型に埋め込むためには，恒等写像に近いものを使うことになる．われわれの使う体系は線型論理の一部になる(あとで示す)．実際，推件$sigma tack tau$において，仮定はただ一つ出現し，函数の引数を交換することは許されない．これを踏まえると，ネストされた含意については深さで添字付けられたdeep inferenceを要する:
#prooftree(
  rule(
    name: $forall_ (n >= 0) R$,
    $sigma tack tau_1 arrow (dots (tau_n arrow tau)dots )$,$sigma tack tau_1 arrow (dots (tau_n arrow forall X.tau)dots)$
  )
)


ただし$X$は$sigma, tau_1 dots tau_n$のいずれにも自由出現しないとする．

subtypingのうち函数型のみを含む場合を考えているので，規則は以上の4つとなる．推移性は単なるcut規則である．この規則がadmissibleであることは後に示す．

#remark(
  
)[
  どのような証明に対してcut除去が可能かは，一般にcut除去定理が成立する体系の部分体系でhaptsatzが成立するとは限らないので，上記の弱い体系では非自明である．
]
#remark("結合子の導入則について")[
  $forall$は相異なる2つの規則$forall L, forall_(n >= 0) R$によって導入される一方，$arrow$は一つの規則によって導入される．そのため，規則の左右の対称性はない．
]

以上の体系が部分型付けを導出するうえで完全かつ整合的であることを示す．体系が部分型付け完全であることを次のようにして示す: $sigma tack tau$が証明可能であることは型を消去すると恒等函数となる型$sigma arrow tau$の項(coercion function)が存在することに必要十分．Mitchellの論文により，これは任意のPERモデルにおける部分型付けであることが保証される．

整合性とは，$sigma tack tau$の証明可能性が$sigma$から$tau$への唯一の型強制の存在を含意することを意味する．ここから，反対称性が従う．実際，$sigma tack tau, tau tack sigma$から2つの型強制函数$iota_1 : sigma arrow tau, iota_2 : tau arrow sigma$が取れる．これらは互いに逆なので，$sigma equiv tau$が従う．整合性の証明は，cut則で拡張された場合はcut admissibilityの証明を要する．

証明項が定義されたとして，この型システムの等式理論を定めることを考えよう．そのためには項の等価性を定義する必要がある．等式の概念はGirardの当初のSystem Fの意味論での定義を一般化し，双対を取ったものとなる．System Fでは型を区別する定義可能な項は存在しない．つまり，$sigma = rho$なるとき1となり，それ以外のとき0となる定義可能な項$J_sigma$が存在しない．

ここから，次の事実が従う: