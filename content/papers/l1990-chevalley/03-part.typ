#import "../../main-defs.typ": *
#import "../../statements.typ": *

получаем #source(18, printed: 331) $3b=0$, $y_(n-1,-n+2)^((n))=b y$, а также
$2t^mu=2b t$, $2z^lambda=b(z-z^2)$. Функции $A,B$ из
@eq:l1990-chevalley-symplectic-penultimate-image сейчас получают запись:

$
  A(x,y)=y x^mu+b y^2 x-y^lambda x,
  quad B(x,y)=2y x^mu-y^2 x^mu+2y x y^lambda.
$

Полагая $x^mu=b x+x^(mu')$, имеем $2K^(mu')=0$. Поскольку $B(x,y)=B(1,x y)$, то
$2x^(mu_1)=x^mu-x^2 dot 1^mu+2x x^lambda$ и

$
  (y^2-y)(x^mu-x^2 dot 1^mu)
  =2x y lr([(x y)^lambda-x^lambda-y^lambda]),
$

$
  (y^2-y)(x^(mu')-x^2 dot 1^(mu'))
  =b(x^3-x)(y^3-y), quad x,y in K.
$

Обе части последнего равенства равны нулю, так как они обращаются в нуль при
умножениях на 2 и 3. Следовательно, для элемента $b$ определён автоморфизм
@eq:l1990-chevalley-c-root-hypercentral группы $U C_n lr((K))$. Умножив $phi$ на
соответствующий автоморфизм, можем считать $b=0$ и, следовательно,

$
  cases(
    2K^mu=2K^(mu_1) cal(J)_2=0 "," quad
    (x+y)^(mu_1)=x^(mu_1)+y^(mu_1)+2^(mu_1) x y,
    2x^(mu_1)=x^mu-a x^2 "," quad
    (y x)^mu=a x y+y x^mu+y^mu x "," quad
    a=1^mu "," quad x","y in K,
    reverse: #true,
  )
$ <eq:l1990-chevalley-symplectic-parameter-identities>

Последнее равенство следует из соотношений $A(x,y)=A(1,x y)$, $1^lambda=0$; они
же показывают, что $x^lambda=a x+x^mu$. Однако преобразованиям $mu,mu_1$ кольца
$K$ с условиями @eq:l1990-chevalley-symplectic-parameter-identities всегда
соответствуют автоморфизмы группы $NC_n lr((K))$ по закону:

$
  cases(
    y epsilon_(n,n-1) arrow.r
    y epsilon_(n,n-1)+(y^mu+a y)epsilon_(n,-n+2),
    y epsilon_(n-1,n-2) arrow.r
    y^mu epsilon_(n-1,-n+1) compose y^(mu_1) epsilon_(n,-n+1)
    compose (-2^(mu_1))y epsilon_(n,-n+2)
    compose y epsilon_(n-1,n-2),
    y epsilon_(n,n-2) arrow.r
    y epsilon_(n,n-2)+y^mu epsilon_(n,-n+1)+y^2 a epsilon_(n,-n)
    quad y in K quad a=1^mu,
    reverse: #true,
  )
$ <eq:l1990-chevalley-symplectic-mu-map>

Таким образом, умножением на автоморфизмы вида
@eq:l1990-chevalley-symplectic-mu-map и вида, соответствующего
@eq:l1990-chevalley-cubic-c-automorphism, можно добиться тождественности $phi$
по модулю центра и на $K epsilon_(n,n-1)$, $K epsilon_(n-1,n-2)$.

Заметим, #source(19, printed: 332) что при $2K=0$ условие
@eq:l1990-chevalley-symplectic-parameter-identities равносильно условию:
$x^mu=a x^2$, $x in K$, $a cal(J)_2 cal(J)_2=0$, $mu_1 in End K^+$ (так что
$mu_1=0$ с точностью до умножения @eq:l1990-chevalley-symplectic-mu-map на
центральный автоморфизм). Если же $cal(Z)_2=0$, то $mu,mu_1$, очевидно, —
нулевые преобразования и отображение @eq:l1990-chevalley-symplectic-mu-map —
единичный автоморфизм.

#enum(numbering: ru-enum, start: 4, [
  Рассматривая, как и в п. «а», образ $K epsilon_(2,-2)$, получим следующие
  равенства по модулю центра:

  $
    (x epsilon_(1,-1))^phi
    =x epsilon_(1,-1)+x^(pi.alt) epsilon_(n,-1),
    quad (x epsilon_(2,-2))^phi
    =(x+x')epsilon_(2,-2)+x^psi epsilon_(n,-2), quad x in K,
  $

  где $pi.alt,prime,psi in End K^+$. Пользуясь тем, что координаты элемента

  $
    (y x epsilon_(2,-1))^phi
    =lr([y epsilon_(2,1),x epsilon_(1,-1)])^phi
    compose (y^2 x epsilon_(2,-2))^phi
    =y x epsilon_(2,-1)+(y^2 x)'epsilon_(2,-2)
    +lr([(y^2 x)^psi+y x^(pi.alt)])epsilon_(n,-2)
  $

  суть функции от произведения $x y$ и, в силу
  @eq:l1990-chevalley-symplectic-coordinate-normalization, $1^(pi.alt)=0$,
  находим: $(cal(J)_2)'=0$, $x^(pi.alt)=(x^2-x)^psi$ и
  $lr([y^2(x^2-x)])^psi=y(x^2-x)^psi$. В силу аддитивности $pi.alt$ имеем
  равенство $2K^psi=0$. Если $n=3$, то

  $
    (y x epsilon_(3,-1))^phi
    =lr([y epsilon_(3,2),x epsilon_(2,-1)])^phi
    =y x epsilon_(3,-1)+y x'epsilon_(3,-2)-y^2 x'epsilon_(3,-3)
  $

  и, следовательно, $x'=1'x$, $1'cal(J)_2=0$. Так как
  $T_(2,-2)=T_(2,-2)^phi=(1+1')K epsilon_(2,-2)+Gamma_2+Z_1$, то $1+1'$ —
  обратимый элемент. С другой стороны, если $a in Ann_K cal(J)_2$ и $1+a$ —
  обратимый элемент, то отображение

  $
    cases(
      x epsilon_(2,-j) arrow.r
      x(epsilon_(2,-j)+a epsilon_(2,-2))
      quad j=1","2 quad x in K,
      x epsilon_(3,-m) arrow.r
      x(epsilon_(3,-m)+a epsilon_(3,-2)+a epsilon_(3,-3))
      quad m=1","3,
      reverse: #true,
    )
  $ <eq:l1990-chevalley-rank-three-shear>

  определяет #source(20, printed: 333) автоморфизм группы $NC_3 lr((K))$.
  (Очевидно $a=0$, когда $K$ — область целостности.) Умножая $phi$ при $n=3$ на
  автоморфизм вида @eq:l1990-chevalley-rank-three-shear, добиваемся условия
  $K'=0$. Когда $n>=4$, это условие всегда выполняется, так как коммутатор
  образов перестановочных элементов $epsilon_(4,2)$, $x epsilon_(3,-1)$ равен
  $x'epsilon_(4,-3)$. При $2<i<n$ имеем

  $
    (y^2 x epsilon_(i,-i))^phi
    =(y x epsilon_(i,-2))^phi
    compose lr([x epsilon_(2,-2),y epsilon_(i,2)])^phi
    =y^2 x epsilon_(i,-i)-y x^psi epsilon_(n,-i),
  $

  откуда $(y^2 x)^psi=y x^psi$. Однако отображением

  $
    cases(
      z epsilon_(i,-i) arrow.r
      z epsilon_(i,-i)+z^psi epsilon_(n,-i)
      quad z epsilon_(i,-1) arrow.r
      z epsilon_(i,-1)+(z^2)^psi epsilon_(n,-i),
      z epsilon_(1,-1) arrow.r
      z epsilon_(1,-1)+(z^2-z)^psi epsilon_(n,-1)
      quad z in K quad 1<i<n,
      reverse: #true,
    )
  $ <eq:l1990-chevalley-symplectic-psi-map>

  определяется автоморфизм группы $NC_n lr((K))$, $n>=3$, для любого
  эндоморфизма $psi$ группы $K^+$ с условием $2K^psi=0$, причём
  $y(x^2-x)^psi=lr([y^2(x^2-x)])^psi$, если $n=3$, и $(y^2 x)^psi=y x^psi$ при
  $n>=4$, $y,x in K$. (Когда $n>=4$ и $K$ — совершенное кольцо характеристики 2,
  очевидно, $x^psi=c sqrt(x)$, $x in K$, для подходящего элемента $c in K$.)
  Поэтому $phi$ есть произведение автоморфизма вида
  @eq:l1990-chevalley-symplectic-psi-map и центрального автоморфизма. Нужно лишь
  заметить, что $NC_n lr((K))=lr(
    chevron.l K epsilon_(j,-j), j=1, 2,
    K epsilon_(i,i-1), 2<=i<=n chevron.r
  )$. Таким образом, доказана
])

#theorem[
  Всякий автоморфизм группы $NC_n lr((K))(approx.eq U C_n lr((K)))$, $n>=3$, над
  коммутативным кольцом $K$ с единицей разложим в произведение диагонального,
  кольцевого, внутреннего, центрального автоморфизмов и автоморфизмов вида
  @eq:l1990-chevalley-symplectic-cd-automorphism при $n>=4$,
  @eq:l1990-chevalley-symplectic-mu-map, @eq:l1990-chevalley-rank-three-shear
  при $n=3$, @eq:l1990-chevalley-symplectic-psi-map и вида, соответствующего
  @eq:l1990-chevalley-cubic-c-automorphism,
  @eq:l1990-chevalley-c-root-hypercentral.
] <th:l1990-chevalley-c-symplectic-automorphisms>

=== #[ ] <sec:l1990-chevalley-high-rank-proof>

Гиперцентральные автоморфизмы групп $U G(K) approx.eq N G(K)$ из теоремы
@th:l1990-chevalley-high-rank-automorphisms описываются, как и в случае $G=C_n$.
Проведём редукцию к ним произвольного автоморфизма $phi$. Случаи
$G=D_4,twisted(2, E_6)$ аналогичны подобным из теоремы
@th:l1990-small-g2-non-three из [@bib:l1990-chevalley-Levchuk1990].

Для классических типов $G$ ранга $>=4$, в силу лемм
@lem:l1990-chevalley-symplectic-central-series–@lem:l1990-chevalley-orthogonal-central-series,
@lem:l1990-chevalley-orthogonal-characteristic-subgroups, можно предполагать
$phi$-инвариантность подгрупп $T_(i,j)$, $i<n$. Отсюда при $G=D_n$, #source(
  21,
  printed: 334,
) $n>=5$, $phi$ индуцирует автоморфизмы фактор-групп
$frac(N D_n lr((K)), T(p_(2m))) approx.eq UT(n, K)$, $m=plus.minus 1$, и
поэтому, в силу теоремы @th:l1983-main-automorphisms из
[@bib:l1990-chevalley-Levchuk1983] и соотношения
@eq:l1990-chevalley-classical-last-root-invariance, $phi$ единичен по модулю
$T_(3,-2)+Gamma_(n-1)$ с точностью до умножения на стандартный автоморфизм. При
$cal(Z)_2=0$, $G=B_n$, $n>=4$, аналогично используем лемму
@lem:l1990-chevalley-orthogonal-central-series и изоморфизм
$frac(N B_n lr((K)), T_(2,-1)) approx.eq UT(n+1, K)$. В группе $N B_3 lr((K))$,
$cal(Z)_2=0$, характеристичны подгруппы $C(Z_2)=T_(1,0)+T_(3,2)$ и
$T_(2,1)=C_(upright(mod) Z_1) Z_3$; здесь $phi$ единичен по модулю коммутанта с
точностью до умножения на автоморфизмы стандартный и вида
@eq:l1990-chevalley-b3-hypercentral.

При $G=twisted(2, A_(2n))$, $n>=2$, $phi$ индуцирует автоморфизмы фактор-группы
$frac(N twisted(2, A_(2n)) lr((K)), T_(1,-1)) approx.eq UT(n+1, K)$;
стандартность $phi$ по модулю $Gamma_2$ для $n>=3$ вытекает непосредственно из
теорем 1–3 [@bib:l1990-chevalley-Levchuk1983] и из
@eq:l1990-chevalley-classical-last-root-invariance. При
$G=twisted(2, A_(2n-1))$, $n>=3$, $phi$ индуцирует автоморфизмы фактор-группы
$frac(N twisted(2, A_(2n-1)) lr((K)), T_(1,-1)) approx.eq UT(n, K)$
и с точностью до умножения на внутренний автоморфизм на подгруппе
$T_(2,-1)+sum_(2<=j<i<=n) K epsilon_(i,j)$ и на её фактор-группе по $T_(2,-2)$,
которая также изоморфна $UT(n, K)$; отсюда, как и выше, получаем стандартность
$phi$ по модулю $Gamma_2$. Для группы $N twisted(2, D_(n+1)) lr((K))$, $n>4$,
$phi$ индуцирует автоморфизмы на фактор-группе по $T_(1,0)$, изоморфной
$UT(n, Ker(1-sigma))$, и на фактор-группе по $T_(3,n-1)$, изоморфной
$U twisted(2, A_3) lr((K))$; при $n=3,4$ к этому приходим, добиваясь вначале
$phi$-инвариантности подгруппы $T_(3,n-1)$ умножением $phi$ на автоморфизмы вида
@eq:l1990-chevalley-root-pair-hypercentral,
@eq:l1990-chevalley-double-root-hypercentral. Стандартность $phi$ по модулю
$Gamma_2$ получаем сейчас, используя описание $Aut U twisted(2, A_3) lr((K))$
для поля $K$ [@bib:l1990-chevalley-Levchuk1990, теорема
@th:l1990-small-unitary-rank-three] и [@bib:l1990-chevalley-Levchuk1983, теоремы
1–3].

Для систем корней типов $E_m$ используем обозначения из
[@bib:l1990-chevalley-Bourbaki1982, таблицы V–VII]; в частности,
$alpha_1,alpha_2,dots$ — простые корни. В группе $U E_6 lr((K))$ централизатор
подгруппы $Z_2$ $C(Z_2)=lr(chevron.l T(alpha_i) | 1<=i<=6, i!=2 chevron.r)$ и
подгруппа $T(alpha_2)$ есть характеристические подгруппы.#ed-note[
  В оригинале приведено неверное равенство
  $T(alpha_2)=C_(upright(mod) Z_1) Gamma_6$: при
  $delta=alpha_1+alpha_3+alpha_4+alpha_5+alpha_6$ этот централизатор равен
  $D=T(alpha_2)X_delta$ (нумерация корней — [@bib:l1990-chevalley-Bourbaki1982,
  таблица V]). Для $H=T(alpha_2)^phi$ имеем $H subset D$ и
  $H Gamma_2=D Gamma_2$, поскольку $T(alpha_2)Gamma_2=D Gamma_2$, а $D$ и
  $Gamma_2$ характеристичны; поэтому проекция $H$ на $alpha_2$ сюръективна.
  Начав с $Gamma_6 subset H$, нисходящей индукцией по высотам $5,4,3,2$ получаем
  $T(alpha_2) inter Gamma_2 subset H$: коммутаторы с цепочками простых корней,
  отличных от $alpha_2$, дают нужный корень с коэффициентом $plus.minus 1$ и
  хвост большей высоты, который устраняется по индукции. Корень $delta$
  централизует подсистему $A_5$; его вклад от сопряжения начинается с высоты 7 и
  уже лежит в $Gamma_6$ (соотношения — [@bib:l1990-chevalley-Carter1972,
  §5.2–5.3]). При $u=alpha_2+alpha_4$, $v=alpha_2+alpha_3+alpha_4+alpha_5$ имеем
  $lr([lr([x_delta lr((t)),x_u lr((1))]),x_v lr((1))])
  =x_theta lr((plus.minus t))$, где $theta$ — максимальный корень, тогда как $H$
  имеет класс нильпотентности 2. Поэтому $delta$-координаты элементов $H$
  нулевые; применение того же рассуждения к $phi^(-1)$ даёт $H=T(alpha_2)$.
] Их пересечение совпадает с $T(alpha_2+alpha_4)$, а фактор-группы
$frac(U E_6 lr((K)), T(alpha_2))$, $C(Z_2)/T(alpha_2+alpha_4)$ изоморфны группе
$UT(6, K)$. Поэтому в силу теоремы @th:l1983-main-automorphisms из
[@bib:l1990-chevalley-Levchuk1983] автоморфизм $phi$ группы $U E_6 lr((K))$
действует по модулю $Gamma_2$ как стандартный автоморфизм на $C(Z_2)$, а также
на всей группе, в силу инвариантности в соотношении
$lr([x_(alpha_2) lr((u)),x_(alpha_4) lr((t))])
=x_(alpha_2+alpha_4) lr((plus.minus u t)) upright(mod) Gamma_3$.

Пусть $phi in Aut U E_7 lr((K))$ и $H=T(alpha_7)^phi$. Подгруппа $T(alpha_7)$
есть максимальная #source(22, printed: 335) абелева нормальная подгруппа группы
$U E_7 lr((K))$, и поэтому

$
  (U_12=)Z_6 subset H subset C(Z_6)
  =lr(
    chevron.l T(alpha_7), T vec("001110", 1),
    T vec("012100", 1) chevron.r
  ).
$

В частности, $H=T(alpha_7) upright(mod) Gamma_4$. Пользуясь включениями
$H supset lr([x_r lr((1)),H])$, $r in Phi^+$, последовательно находим
$H inter Gamma_i supset T(alpha_7) inter Gamma_i$, $i=11,10,9,8,7,6$, откуда
$H subset C(T(alpha_7) inter Gamma_6)=(T(alpha_7))$ и $T(alpha_7)$ —
характеристическая подгруппа. Поскольку
$C_(upright(mod) Z_1) lr((Gamma_10))=T(alpha_1)Gamma_7$, то
$T(alpha_1)^phi=T(alpha_1) upright(mod) Gamma_7$ и

$
  lr([T(alpha_1)^phi,Gamma_3])=lr([T(alpha_1),Gamma_3])
  subset T(alpha_1) subset
  C_(upright(mod) Z_1) lr((lr([T(alpha_1),Gamma_3])))=T(alpha_1),
$

т. е. $T(alpha_1)$ — также характеристическая подгруппа. Поэтому $phi$
индуцирует автоморфизмы на фактор-группах группы $U E_7 lr((K))$ по нормальным
подгруппам $T(alpha_7)$, $T(alpha_1)$, которые изоморфны соответственно
$U E_6 lr((K))$ и $U D_6 lr((K))$. Используя утверждения теоремы
@th:l1990-chevalley-high-rank-automorphisms для $G=D_6,E_6$, получаем
стандартность $phi$ по модулю коммутанта.

Подгруппа $T(alpha_8)$ группы $U E_8 lr((K))$ содержит $Gamma_18$ и является
максимальной абелевой по модулю $Z_1$. Поэтому для $phi in Aut U E_8 lr((K))$
имеем $T(alpha_8)^phi subset C_(upright(mod) Z_1) lr((Gamma_18))$, откуда
$T(alpha_8)^phi=T(alpha_8) upright(mod) Gamma_10$. Учитывая нормальность
$T(alpha_8)$, получаем

$
  T(alpha_8) inter Gamma_9=lr([T(alpha_8),Gamma_8])
  =lr([T(alpha_8)^phi,Gamma_8]) subset T(alpha_8)^phi
  subset C_(upright(mod) Z_1) lr((T(alpha_8) inter Gamma_9))=T(alpha_8).
$

Поэтому $T(alpha_8)$, а также
$C(Z_2)=lr(chevron.l T(alpha_i) | 1<=i<=7 chevron.r)$ — характеристические
подгруппы. Их пересечение равно $T(alpha_7+alpha_8)$, причём

$
  frac(U E_8 lr((K)), T(alpha_8)) approx.eq C(Z_2)/T(alpha_7+alpha_8)
  approx.eq U E_7 lr((K)).
$

Отсюда (как и для $U E_6 lr((K))$) $phi$ есть гиперцентральный с точностью до
умножения #source(23, printed: 336) на диагональный, кольцевой и внутренний
автоморфизм. Доказательство теоремы @th:l1990-chevalley-high-rank-automorphisms
завершено.

=== #[ ] <sec:l1990-chevalley-characteristic-subgroups>

Выделим характеристические подгруппы группы $U Phi(K)$ над полем $K$. Если
$2K=0$, $Phi=B_2,F_4$ или $3K=0$, $Phi=G_2$, будем предполагать, что $K$ есть
совершенное поле характеристики соответственно 2 или 3, что обеспечивается
наличием графового автоморфизма в указанных случаях. Подгруппу группы $U Phi(K)$
называют симметричной, если она выдерживает все графовые автоморфизмы. Через $W$
обозначим совокупность симметрических нормальных подгрупп группы $U Phi(K)$, в
которых корневые подгруппы образуют нормальный базис
[@bib:l1990-chevalley-Levchuk1982]. Очевидно, $W$ содержит класс симметричных
подгрупп, которые порождаются подгруппами вида $T(r)$, $r in Phi^+$, и даже
совпадает с этим классом, если характеристика поля равна нулю или $>rho(Phi)$; в
общем случае совпадения нет.

#theorem[
  Класс $Omega$ всех характеристических подгрупп группы $U Phi(K)$ совпадает с
  $W$, за исключением следующих случаев:

  #enum(
    numbering: ru-enum,
    [
      в группе $U Phi(2)$, $Phi!=B_2,G_2,A_3,D_4$, характеристичны все
      нормальные симметричные подгруппы, выдерживающие гиперцентральные
      автоморфизмы;
    ],
    [
      в группе $NC_n lr((K))(approx.eq U C_n lr((K)))$, $|K|>2$, $n>=2$,
      характеристичны в точности подгруппы $H in W$ с условием
      $H supset H_(n,n-1)epsilon_(n-1,-n+2)
      +H_(n,n-2)epsilon_(n-1,-n+1)$, если $n>=3$, $K=GF(3)$, и
      $H supset H_(n,n-1)epsilon_(n-1,-n+1)$, если $K=2K=3K$ ($H_(i,j)$ —
      $(i,j)$-проекция $H$);
    ],
    [
      в группе $N B_3 lr((3))$ характеристичны в точности подгруппы $H in W$ с
      условием $H supset H_(1,0)epsilon_(3,2)+H_(2,0)epsilon_(3,1)
      +H_(2,-1)epsilon_(3,0)$;
    ],
    [
      $Omega={1,Gamma_2,Z_1,Gamma_1}$ для группы $U B_2 lr((2))$, а для
      $U G_2 lr((3))$ $Omega=W union {Gamma_2,X_alpha X_beta Gamma_2}$;
    ],
    enum.item(6)[
      для группы $U G_2 lr((4))$ класс $Omega=W without {T(2alpha+beta)}$, а для
      группы $U G_2 lr((2))$ сюда добавляются ещё подгруппы $Gamma_2$ и
      $x_alpha lr((1))x_(alpha+beta) lr((k))Gamma_2$, $k=0,1$.
    ],
  )
] <th:l1990-chevalley-normal-type-characteristic-subgroups>

#proof[
  Для групп малых рангов $Phi$ очевидно. Автоморфизмы группы $U Phi(2)$,
  $Phi!=G_2,A_3,D_4$, порождаются графовыми, внутренними и гиперцентральными
  автоморфизмами; группа $U B_2 lr((2))$ исключительна, поскольку её коммутант
  строго лежит в центре. (См. полуграфовые автоморфизмы
  [@bib:l1990-chevalley-Levchuk1990, замечание @rem:l1990-small-b2-small-fields]
  и автоморфизмы @eq:l1990-chevalley-root-pair-hypercentral,
  @eq:l1990-chevalley-double-root-hypercentral.)

  Несложно #source(24, printed: 337) убедиться, что все нормальные симметричные
  подгруппы $H$ группы $U Phi(K)$, выдерживающие диагональные автоморфизмы,
  лежат в $W$ при $|K|>2$, $Phi!=G_2$, и в случае $Phi=G_2$, $|K|>=4$; когда
  $|K|>rho(Phi)+1$, это следует и из теоремы 3
  [@bib:l1990-chevalley-Levchuk1982]. Для характеристичности подгруппы $H$
  группы $U C_n lr((K))$, $|K|>2$, или группы $U B_3 lr((3))$ остаётся
  потребовать инвариантность относительно автоморфизмов
  @eq:l1990-chevalley-cubic-c-automorphism,
  @eq:l1990-chevalley-c-root-hypercentral и соответственно
  @eq:l1990-chevalley-b3-hypercentral. В остальных случаях для групп $U Phi(K)$
  ранга $>=3$, $|K|>2$, очевидно, имеем $Omega=W$. Теорема доказана.
]

Аналогично описываются характеристические подгруппы скрученных групп $U G(K)$.

#theorem[
  Нормальные подгруппы скрученной группы $U G(K)$ ранга $>=1$ над полем $K$,
  выдерживающие диагональные автоморфизмы, порождаются подгруппами $T_(i,j)$ или
  $T(r)$, $r in twisted(n, Phi)$ (см. [@bib:l1990-chevalley-Levchuk1990, §
  @sec:l1990-small-twisted-f4 и § @sec:l1990-small-central-series]) и являются
  характеристическими подгруппами. Исключениями являются группы
  $U twisted(2, Phi)(4)$, $Phi=D_n$, $n>=4$, или $E_6$. В них нормальная
  подгруппа $H$ выдерживает диагональные автоморфизмы тогда и только тогда,
  когда $H supset T(r)$ при условии, что $r$-проекция $H$ — ненулевая и
  $r={alpha,overline(alpha)}$, $alpha in Phi$, $alpha!=overline(alpha)$; для
  характеристичности $H$ достаточно потребовать ещё при $Phi=D_n$ инвариантность
  $H$ относительно автоморфизмов вида
  @eq:l1990-chevalley-double-root-hypercentral.
] <th:l1990-chevalley-twisted-characteristic-subgroups>
