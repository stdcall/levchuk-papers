#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "diagrams/b-f4-roots.typ": f4-roots

#proof[
  Пусть $phi in Aut U G_2(K)$,
  $x_alpha^phi lr((t)) = x_alpha lr((t^(lambda_0))) x_beta lr((t^(lambda')))
  x_(alpha+beta) lr((t^(lambda_1))) mod U_3$. Подгруппа $U_2 = Z_2$
  характеристична, и поэтому с точностью до умножения $phi$ на графовый и
  диагональный автоморфизмы $1^(lambda_0) = 1$. Вычислив произведение
  $x_alpha^phi lr((t)) x_alpha^phi lr((z))$, находим
  $
    (z+t)^(lambda_1) = z^(lambda_1) + t^(lambda_1)
    + z^(lambda_0) t^(lambda'),
    quad t^(lambda') = 1^(lambda') t^(lambda_0), quad z,t in K,
  $
  а также $(z^(lambda_0))^3 t^(lambda') = (t^(lambda_0)) z^(lambda')$, т.~е.
  $1^(lambda') z^(lambda_0) t^(lambda_0)
  (z-t)^(lambda_0) (z+t)^(lambda_0) = 0$. Ясно, что $lambda_0 in Aut K^+$ и при
  $|K| > 3$ должны иметь равенства $1^(lambda') = 0, lambda' = 0$; когда
  $K = GF(3)$, эти равенства получаем с помощью соотношения
  $[x_alpha^phi lr((1))]^3 = 1$. Аналогично
  $x_beta^phi lr((t)) = x_beta lr((t^(mu_0))) mod U_2$, $1^(mu_0) = 1$, и для
  элементов $x_alpha^phi lr((t))$, $x_beta^phi lr((t))$ можем использовать
  обозначения из доказательства теоремы @th:l1990-small-g2-non-three. Равенства
  $
    x_(2alpha+beta)^phi lr((s u t))
    = [x_alpha lr((s)), [x_beta lr((u)), x_alpha lr((t))]]^phi
    = x_(2alpha+beta) lr((u^(mu_0) t^(lambda_0) s^(lambda_0))),
    quad u,t,s in K,
  $
  показывают, что $u^(mu_0) t^(lambda_0) s^(lambda_0)$ — функция от произведения
  $s u t$. Отсюда $lambda_0$ — автоморфизм поля $K$ и $mu_0 = lambda_0$. Умножив
  $phi$ на кольцевой, внутренний и вида @eq:l1990-small-g2-extremal
  автоморфизмы, получим
  $lambda_0 = mu_0 = 1, 1^(lambda_1) = 1^(mu_1) = 1^(mu_3) = 0$. Поскольку
  $(z+t)^(lambda_2) = z^(lambda_2) + t^(lambda_2)
  + z t^(lambda_1)$, то $t^(lambda_1) = 1^(lambda_1) t = 0$; аналогично
  $mu_3 = 0$. Если $K = GF(3)$, то, умножая $phi$ на автоморфизм
  @eq:l1990-small-g2-characteristic-three-map с $mu = psi = 0$, можно сделать
  $phi$ центральным автоморфизмом, единичным на коммутанте. При $|K| > 3$ $phi$
  единичен на центре и
  $
    x_(alpha+beta)^phi lr((u t)) x_(3alpha+beta)^phi lr((-u t^3))
    = x_(alpha+beta) lr((u t)) x_(3alpha+beta) lr((-u t^3))
    x_(2alpha+beta) lr((-u^(mu_1) t)) x_(3alpha+2beta) lr((u t^(lambda_3))).
  $

  Умножая этот элемент на элементы, полученные при заменах $(u,t)$ на $(-u t,1)$
  или $(-u t^3,1)$, находим $x_(alpha+beta)^phi lr((v))$,
  $x_(3alpha+beta)^phi lr((v))$ для $v = u(t-t^3)$, а также равенства
  $
    u(t-t^3)d = u(t^(lambda_3) - t 1^(lambda_3)),
    quad t^(lambda_3) = f t - d t^3, quad u,t in K,
  $
  #source(10, printed: 149)для некоторого $d in K$ и $f = 1^(lambda_3) + d$.
  Кроме того, должно выполняться условие @eq:l1990-small-g2-additive-condition
  при $mu = mu_1$. Поэтому $phi$ есть произведение центрального и вида
  @eq:l1990-small-g2-characteristic-three-map автоморфизмов. Теорема доказана.
]

=== #[ ] <sec:l1990-small-twisted-rank-two>

Отметим, что стандартный центральный ряд в скрученной группе
$U twisted(n, Phi_sigma) lr((K))$ образуют её пересечения с подгруппами $U_i$
группы $U Phi(K)$, выделяемыми, как и выше. Справедлива

#lemma[
  Верхний и нижний центральные ряды группы $U twisted(n, Phi_sigma) lr((K))$
  совпадают со стандартным центральным рядом, когда $K$ — поле.
] <lem:l1990-small-twisted-central-series>

Автоморфизм $sigma: t -> overline(t)$ кольца $K$, участвующий в построении
группы $U twisted(n, Phi) lr((K))$, в её обозначении будем опускать. Из
определения группы $U twisted(2, A_3) lr((K))$ (см., например,
[@bib:l1990-small-Carter1972]) следует, что её можно отождествить с подгруппой
унитреугольной группы $UT(4, K)$, порождённой элементами
$e + u epsilon_32 = x_beta lr((u))$,
$e + u epsilon_41 = x_(2alpha+beta) lr((u))$ $(u in Ker(1-sigma))$,
$e + t epsilon_21 - overline(t) epsilon_43 = x_alpha lr((t))$,
$e + t epsilon_31 + overline(t) epsilon_42 = x_(alpha+beta) lr((t))$ $(t in K)$.
При этом
$
  [x_beta lr((u)), x_alpha lr((t))]
  = x_(alpha+beta) lr((u t)) x_(2alpha+beta) lr((u t overline(t))),
  quad [x_(alpha+beta) lr((s)), x_alpha lr((t))]
  = x_(2alpha+beta) lr((t overline(s) + s overline(t))).
$

#theorem[
  Всякий автоморфизм группы $U twisted(2, A_3) lr((K))$ над полем $K$ есть
  произведение стандартного автоморфизма и автоморфизма
  $
    x_alpha lr((t)) -> x_alpha lr((t)) x_(alpha+beta) lr((2 overline(k t)))
    x_(2alpha+beta) lr((k t^2 + overline(k) overline(t)^2)), quad t in K
  $ <eq:l1990-small-unitary-extremal>
  (при $2K = K$) с произвольным $k in K$.
] <th:l1990-small-unitary-rank-three>

#proof[
  Подгруппы $Z_i$, $C(Z_2) = X_beta Z_2$ — характеристические. Поэтому для
  автоморфизма $phi$ имеем
  $
    x_beta^phi lr((u)) = x_beta lr((u^mu)) x_(alpha+beta) lr((u^(mu_1)))
    x_(2alpha+beta) lr((u^(mu_0))),
    quad x_(2alpha+beta)^phi lr((u)) = x_(2alpha+beta) lr((u^psi)),
  $
  $
    x_alpha^phi lr((t)) = x_alpha lr((t^lambda)) x_beta lr((t^(lambda')))
    x_(alpha+beta) lr((t^(lambda_1))) x_(2alpha+beta) lr((t^(lambda_0))),
    quad u = overline(u), quad t in K,
  $
  причём $1^lambda = 1^mu = 1$, с точностью до умножения на диагональный
  автоморфизм. Ясно, что $lambda in Aut K^+$. Поскольку
  $(s+t)^(lambda_1) = s^(lambda_1) + t^(lambda_1)
  + s^lambda t^(lambda')$, $s,t in K$, то
  $t^(lambda') = 1^(lambda') t in Ker(1-sigma)$ и, следовательно,
  $1^(lambda') K^(1-sigma) = 0$, $lambda' = 0$. Равенства
  $
    x_(alpha+beta)^phi lr((u t))
    = x_(alpha+beta) lr((u^mu t^lambda))
    x_(2alpha+beta) lr(
      [u^mu t^lambda overline(t^lambda) - (u t overline(t))^psi
        - (overline(t^lambda) u^(mu_1))^(1+sigma)]
    )
  $ <eq:l1990-small-unitary-root-image>
  $(u = overline(u), t in K)$ показывают, что $u^mu t^lambda = (u t)^lambda$; в
  частности, ограничение $lambda$ на подполе $Ker(1-sigma)$ является его
  автоморфизмом и совпадает с $mu$. Вычислив коммутатор
  $[x_(alpha+beta)^phi lr((s)), x_alpha^phi lr((t))]$, находим #source(
    11,
    printed: 150,
  )$
    (s overline(t) + overline(s) t)^psi
    = s^lambda overline(t^lambda) + overline(s^lambda) t^lambda,
    quad (overline(t)+t)^psi = overline(t^lambda) + t^lambda,
    quad s,t in K.
  $ <eq:l1990-small-unitary-trace-identity>

  При $2K = K$ для $v = overline(v)$ отсюда находим $(2v)^psi = 2v^lambda$,
  $psi = mu$ и, следовательно,
  $(overline(t)+t)^lambda = overline(t^lambda) + t^lambda$,
  $sigma lambda = lambda sigma$. В силу @eq:l1990-small-unitary-trace-identity
  $
    (overline(t) t)^lambda = overline(t^lambda) t^lambda,
    quad (t^lambda)^(-1)
    = overline(t^lambda) [(overline(t) t)^mu]^(-1)
    = overline(t^lambda) [(overline(t) t)^(-1)]^mu = (t^(-1))^lambda,
    quad t in K,
  $
  и, по теореме Хуа [@bib:l1990-small-Artin1969, с. 58], $lambda$ есть
  автоморфизм поля $K$. Умножив $phi$ на кольцевой, внутренний и вида
  @eq:l1990-small-unitary-extremal автоморфизмы, получим $lambda = 1$,
  $1^(mu_1) = 1^(lambda_1) = 0$. Из @eq:l1990-small-unitary-root-image вытекает
  единичность $phi$ на коммутанте (полагаем $u = 1$), а также равенства
  $(u^(mu_1) overline(t))^(1+sigma) = 0 = u^(mu_1(1+sigma))
  = u^(mu_1) t^(1-sigma)$ $(t in K)$, т.~е. $mu_1 = 0$. Изоморфизм
  $X_alpha approx K^+$ даёт симметричность выражения
  $(s t^(lambda_1))^(1+sigma)$ по $s,t in K$. Отсюда
  $t^(lambda_1(1+sigma)) = 0$, $t^(lambda_1) = d t^(sigma-1)$ для некоторого
  $d = overline(d) in K$. Но тогда $phi$ есть произведение центрального,
  внутреннего и вида @eq:l1990-small-unitary-extremal автоморфизмов.

  Пусть $2K = 0$. Тогда изоморфизм $X_alpha approx K^+$ даёт симметричность по
  $s,t in K$ выражения $(overline(s^lambda) t^(lambda_1))^(1+sigma)$ и его
  равенство нулю при $s = t$. В частности, $1^(lambda_1) in Ker(1-sigma)$, и
  равенства $1^(lambda_1) = 1^(mu_1) = 0$ здесь получаем, умножая $phi$ на
  внутренний автоморфизм. Отсюда находим $d = overline(d) in K$, при котором
  $t^(lambda_1) = d t^(lambda(1+sigma))$ и, следовательно,
  $d[t^(lambda(1+sigma))]^2 = 0$ $(t in K)$, $d = 0$, $lambda_1 = 0$.

  Зафиксируем элемент $i in K without P$, $P = Ker(1-sigma)$, а элементы
  $c,c_1,m,k in P$ определим равенствами $overline(i) = i + c$,
  $i^2 = c i + c_1$, $i^lambda = m i + k$. Произвольный элемент $t in K$
  представим в виде $t = z + i v$ $(z,v in P)$. Учитывая
  @eq:l1990-small-unitary-trace-identity, находим
  $(overline(t)+t)^psi = (c v)^psi = overline(t^lambda) + t^lambda
  = v^lambda m c$, откуда $v^psi = v^lambda q$, $q = m c (c^(-1))^lambda$. Далее
  замечаем, что элемент @eq:l1990-small-unitary-root-image не изменяется при
  замене $(u,t) -> (1,u t)$ и поэтому
  $
    (t^lambda u^(mu_1 sigma))^(1+sigma)
    = [overline(t) t (u^2-u)]^psi
    + t^lambda t^(lambda sigma) (u-u^2)^lambda,
  $
  $
    u^(mu_1(sigma+1)) = (u^2-u)^lambda lr((q+1)),
    quad u^(mu_1) t^(lambda(sigma+1))
    = (u^2-u)^lambda lr(
      [(overline(t) t)^lambda q
        + t^lambda t^(lambda sigma) + t^lambda lr((q+1))]
    ).
  $

  В частности, $u^(mu_1) = (u^2-u)^lambda lr((f+i g))$ для некоторых $f,g in P$.
  Если $|P| = 2$, то $K = GF(4)$ и $lambda$ — автоморфизм поля $K$,
  перестановочный с $sigma$. При $|P| > 2$ имеем
  $
    g v^lambda m c = v^lambda m(q+1), quad g = (q+1)c^(-1),
  $
  $
    f m c v^lambda & = (z^2+z)^lambda lr((q-1)) \
                   & + v^lambda lr([(c z)^lambda q + z^lambda m c + k(q+1)])
                     + (v^lambda)^2 (q c_1^lambda + k^2 + c_1 m^2 + m k c).
  $
  #source(12, printed: 151)Последнее равенство как многочлен от $v^lambda$ имеет
  степень $<= 2$ и является нулевым многочленом, поскольку $v^lambda$ может
  принимать любое значение из $P$. Приравнивая к нулю свободный член, получим
  $q = 1$ и, следовательно, $psi = mu$, $lambda sigma = sigma lambda$,
  $c^lambda = m c$. Сравнивая коэффициенты при $v^lambda$, находим $f = 0$,
  $mu_1 = 0$, а также $(overline(t) t)^lambda = t^lambda overline(t^lambda)$.
  Отсюда, как и выше, $(t^(-1))^lambda = (t^lambda)^(-1)$ и, по теореме Хуа,
  $lambda$ есть автоморфизм поля $K$, а $phi$ — произведение кольцевого и
  центрального автоморфизмов. Теорема доказана.
]

*Замечания.*
#enum(
  numbering: "1)",
  [#remark-item[
    Группа $Aut U twisted(2, A_4) lr((K))$, $K$ — поле, аналогично порождается
    стандартными автоморфизмами и автоморфизмами, которые индуцируются
    произведениями автоморфизмов вида @eq:l1990-small-extremal-automorphism
    группы $U A_4(K)$.
  ] <rem:l1990-small-unitary-rank-four>],
  [#remark-item[
    Автоморфизмы группы $U B_2(K)$ над полем $K$ при $3K = 0$ стандартны; для
    конечного поля $K$ характеристики 2 они порождаются стандартными
    автоморфизмами и ещё, когда $K = GF(2)$ или $GF(4)$, полуграфовыми
    автоморфизмами
    $
      x_alpha lr((t)) -> x_alpha lr((t^2)),
      quad x_(alpha+beta) lr((t)) -> x_(2alpha+beta) lr((t)),
      quad x_(2alpha+beta) lr((t)) -> x_(alpha+beta) lr((t)).
    $
  ] <rem:l1990-small-b2-small-fields>],
  [#remark-item[
    Скрученную группу $U twisted(3, D_(4,sigma)) lr((K))$ ассоциируют с системой
    корней типа $G_2$, например, [@bib:l1990-small-Carter1972]; таким образом, в
    ней естественно выделяются порождающие «корневые» элементы
    $
      x_r lr((t)) quad (t in K, quad r in {alpha,alpha+beta,2alpha+beta}),
      quad x_s lr((v)) quad (v = overline(v) in K,
        quad s in {beta,3alpha+beta,3alpha+2beta}).
    $
    Всякий автоморфизм группы $U twisted(3, D_(4,sigma)) lr((K))$ над конечным
    полем $K$ есть произведение стандартного [@bib:l1990-small-Gibbs1970, § 8] и
    вида @eq:l1990-small-extremal-automorphism автоморфизмов и при $K = GF(8)$
    автоморфизма
    $
      x_beta lr((u)) -> x_beta lr((u)) x_(2alpha+beta) lr((k u)),
    $
    $
      x_(alpha+beta) lr((t)) -> x_(alpha+beta) lr((t))
      x_(3alpha+beta) lr(((k overline(t))^pi)) x_(3alpha+2beta) lr(((k t)^pi))
    $
    $(u = overline(u), t in K)$, где $k$ — произвольный элемент из $K$,
    $pi = 1 + sigma + sigma^2$.
  ] <rem:l1990-small-triality-small-field>],
)

=== #[ ] <sec:l1990-small-f4-automorphisms>

Если $r$ — короткий корень максимальной высоты в системе корней $Phi = F_4$ (или
$B_n$, $n >= 3$) и $cal(Z)_2 = 0$, то для всякого $c in K$ сопряжение элементом
$x_r lr((c/2))$ определяет автоморфизм группы $U Phi(K)$, называемый
полувнутренним; внутренний он лишь при $c/2 in K$.

#theorem[
  Всякий автоморфизм $phi$ группы $U F_4(K)$ над кольцом $K$ #source(
    13,
    printed: 152,
  )с условием $cal(Z)_2 = 0$ есть произведение стандартного, полувнутреннего и
  вида @eq:l1990-small-extremal-automorphism автоморфизмов.
] <th:l1990-small-f4-automorphisms>

#proof(head: none)[
  а) Построим $K$-алгебру с базисом Шевалле ${e_r quad (r in Phi), ...}$,
  соответствующим системе корней $Phi$ (см., например,
  [@bib:l1990-small-Carter1972, § 4.4]), и пусть $N Phi(K)$ — подмодуль с
  базисом $e_r$ $(r in Phi^+)$. Фиксируя каноническое разложение элемента
  $A in U Phi(K)$ в произведение корневых элементов $x_r lr((t_r))$,
  $r in Phi^+$ [@bib:l1990-small-Carter1972, 5.3.3(ii)], положим
  $pi(A) = sum_(r in Phi^+) t_r e_r$. Равенства $alpha compose beta = pi(
    pi^(-1) lr((alpha))
    pi^(-1) lr((beta))
  )$ определяют групповую операцию на $N Phi(K)$, причём
  $N Phi(K) approx U Phi(K)$. Полагаем $L_i = pi(U_i)$, и если $M subset Phi$,
  то $L_i lr((M)) = chevron.l K e_r | e_r in L_i, quad r in.not M chevron.r$.
  Положим также $T(s) = chevron.l K e_r | r in Phi^+, quad r-s$ — линейная
  комбинация простых корней с неотрицательными коэффициентами $chevron.r$,
  $s in Phi$.

  Систему положительных корней типа $B_n$, $C_n$ или $D_n$ в евклидовом
  пространстве с ортонормированным базисом $epsilon_1,epsilon_2,...,epsilon_n$
  (см. [@bib:l1990-small-Bourbaki1982, таблицы II–IV]) можно составить из корней
  вида $epsilon_i - m epsilon_j$, $1 <= j <= i <= n$, $m in {-1,0,1}$; такой
  корень обозначим через $p_(i,m j)$ при $Phi = C_n$ и через $q_(i,m j)$ при
  $Phi = B_n$. Система положительных корней типа $F_4$ является объединением
  систем $B_4^+ = {q_(i j) | 0 <= |j| < i <= 4}$ и
  $C_4^+ = {p_(i j) | 0 < |j| <= i <= 4, quad i != j}$. Пересечение
  $B_4^+ inter C_4^+ = {q_(i 0),p_(i,-i) quad (1 <= i <= 4)}$ определено на
  диаграмме. (Корни высоты $> 2$ сопровождаются обозначением (abcd), принятым в
  [@bib:l1990-small-Bourbaki1982, таблица VIII].) Когда корни $r,s,r+s$ из
  $F_4^+$ не лежат одновременно в одной из систем $B_4^+$, $C_4^+$, то они
  обязаны лежать в одной из следующих подсистем типа $B_2$:
  $
    {p_(3,-v), q_(3,2v), p_(4,2v), q_(4v)},
    quad {p_(3,2v), q_(3,-v), p_(4v), q_(4,2v)},
  $
  $
    {p_(3v), q_(3v), p_(4,2v), q_(4,2v)},
    quad {p_(3,2v), q_(3,-2v), p_(4,-v), q_(4v)},
    quad |v| = 1.
  $
  Симметрия системы $F_4^+$, индуцированная симметрией 2-го порядка графа
  Кокстера, имеет здесь особенно простую запись. (Ср. с
  [@bib:l1990-small-Hartley1984].)

  Несложно найти центральные ряды группы $N F_4(K)$. Договоримся обозначать
  одним символом корень $r in F_4^+$ и соответствующий ему элемент базиса
  Шевалле. Тогда определено отображение $overline(quad)$ элементов базиса
  Шевалле; $tau$ — его продолжение до автоморфизма $K$-модуля $N F_4(K)$. Другие
  обозначения взяты из леммы @lem:l1990-small-g2-central-series.
]

$ #source(14, printed: 153)#f4-roots() $
<pass:l1990-small-f4-root-representation>

#lemma[
  В группе $N F_4(K)$ $(U F_4(K))$ выполняются равенства:
  $
    Gamma_2 = L_2 lr((q_(2,-1),p_(2,-1))) + K(q_(2,-1)+p_(2,-1))
    + cal(J)_2 q_(2,-1),
  $
  $
    Gamma_3 = L_4 lr((q_(3,-1),q_(4 3))) + 2K q_(2,-1)
    + K(q_(3,-1)+p_(4 3)) + cal(J)_2 q_(3,-1)
    + K(p_(3,-1)+q_(4 3)) + cal(J)_2 p_(3,-1),
  $
  $
    Gamma_4 = L_5 lr((q_(4 3),q_(4 2))) + K p_(3,-2)
    + K(p_(4 2)+q_(4 2)) + cal(J)_2 q_(4 2)
    + 2K q_(3,-1) + 2K q_(4 3),
  $
  $
    Gamma_i = L_(i+2) + L_(i+2)^tau + (2K) dot L_i quad (i = 5,6),
  $
  $
    Gamma_i = L_(i+3) + L_(i+3)^tau + (2K) dot L_i quad (i = 7,8),
  $
  #source(15, printed: 154)$
    Gamma_i = (2K) dot L_i quad (9 <= i <= 11), quad Gamma_12 = 0;
  $
  $
    Z_i = L_(12-i) + cal(Z)_2 dot L_(12-i)^tau quad (i = 1,2,3),
    quad Z_4 = L_8 + cal(Z)_2 dot (L_7 + L_7^tau),
  $
  $
    Z_5 = L_7 + cal(Z)_2 dot L_4 lr((q_(3,-1),q_(4 3))),
    quad Z_6 = L_6 + cal(Z)_2 lr((L_4 + L_4^tau)),
  $
  $
    Z_7 = L_5 + cal(Z)_2 dot L_2,
    quad Z_i = L_(12-i) + cal(Z)_2 dot L_1 quad (8 <= i <= 11).
  $
] <lem:l1990-small-f4-central-series>

#proof(head: none)[
  б) Ясно, что
  $C(Z_2) = T(q_(2 1)) + T(p_(2 1)) + (Ann_K cal(Z)_2) dot T(p_(3 2))$ —
  характеристическая подгруппа. Подгруппа $T(q_(3 2))^phi$ по модулю $Z_1$
  является максимальной абелевой нормальной подгруппой группы $N F_4(K)$. При
  $cal(Z)_2 = 0$ она содержит $Z_6 = L_6$ и потому лежит в
  $T(q_(3 2)) + K q_(4 3)$. Однако $q_(4 3)$-проекция подгруппы $T(q_(3 2))^phi$
  равна нулю, поскольку она совпадает с $q_(4 1)$-проекцией множества
  $[[T(q_(3 2))^phi,q_(2 1)],T(q_(3 2))^phi] subset Z_1$. Следовательно,
  $T(q_(3 2))$ и $T(p_(3 2)) + T(q_(2,-1)) = C(Z_4)$ — характеристические
  подгруппы. Фактор-группы по ним изоморфны соответственно $NC_3(K)$ и
  $UT(4, K)$. Используя теорему @th:l1983-rank-four
  [@bib:l1990-small-Levchuk1983] и характеристичность
  $C(Z_3) = T(p_(3 2)) + T(q_(2 1))$, устанавливаем, что автоморфизм $phi$
  группы $N F_4(K)$ единичен по модулю $L_3$ с точностью до умножения на
  стандартный автоморфизм. Умножением на внутренний и полувнутренний
  автоморфизмы с помощью инвариантности основных соотношений несложно добиться
  тождественности $phi$ на $q_(3 2)$ по модулю $Z_2 = L_10$ и на $p_(3 2)$,
  $p_(2 1)$, $q_(2 1)$ по модулю центра. Тогда умножением на центральный
  автоморфизм $phi$ приводится к автоморфизму вида
  @eq:l1990-small-extremal-automorphism. Это доказывает теорему
  @th:l1990-small-f4-automorphisms.

  в) Обозначим «корневой» элемент группы $U twisted(2, E_6) lr((K))$ тем же
  символом, что и соответствующий элемент $N F_4(K)$. (Граф Кокстера системы
  корней типа $E_6$ (см. [@bib:l1990-small-Bourbaki1982, таблица V])
  скручивается по правилу: $q_(3 2) = {alpha_2}$, $q_(2 1) = {alpha_4}$,
  $p_(2 1) = {alpha_3,alpha_5}$, $p_(3 2) = {alpha_1,alpha_6}$.) Тогда
  $U twisted(2, E_6) lr((K)) = chevron.l x p_(i v), y q_(i v) |
  1 <= |v| < i <= 4, quad y = overline(y), quad x in K chevron.r$. Предполагая,
  что $K$ — поле, можем применять лемму @lem:l1990-small-twisted-central-series.
  Формулы централизаторов $C(Z_i)$ здесь такие же, как и в «б». Аналогично
  исследуется и автоморфизм $phi$ группы $U twisted(2, E_6) lr((K))$. В
  частности, он индуцирует автоморфизм на фактор-группе по
  $C_(mod Z_2) lr((Z_5)) = T(q_(3 2)) + T(q_(2 1))$, которая изоморфна
  $UT(3, K)$, и на
  $U twisted(2, E_6) lr((K)) slash C(Z_3) approx UT(3, Ker(1-sigma))$.
  Умножением автоморфизма $phi$ на диагональный, кольцевой и внутренний
  автоморфизмы можно добиться, используя теорему @th:l1983-rank-three
  [@bib:l1990-small-Levchuk1983], тождественности $phi$ по модулю $Z_3$.
]
