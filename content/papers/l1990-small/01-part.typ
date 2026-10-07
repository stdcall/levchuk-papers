#import "../../main-defs.typ": *
#import "../../statements.typ": *

#heading(level: 3, numbering: none)[Введение] <sec:l1990-small-introduction>

#source(2, printed: 141)Пусть $U G(K)$ — унипотентная подгруппа группы Шевалле
нормального или скрученного типа $G (= Phi$ или $twisted(n, Phi))$ над
коммутативным кольцом $K$ с 1 (см. [@bib:l1990-small-Carter1972, § 5.1 и 13.6]).
Её автоморфизмы (наряду с коммутаторным строением) изучены, когда $K$ — поле
характеристики $!= 2, 3$ (см. [@bib:l1990-small-Gibbs1970]) или $G = A_n$ (см.
[@bib:l1990-small-Levchuk1983]); см. также проблему (1.5), записанную в
[@bib:l1990-small-Kondratyev1986].

Цель статьи — исследовать автоморфизмы и центральные ряды групп $U D_4(K)$,
$U F_4(K)$, $U twisted(2, E_6) lr((K))$ (см. §
@sec:l1990-small-f4-automorphisms, @sec:l1990-small-f4-perfect,
@sec:l1990-small-d4), а также групп $U G(K)$ над кольцом $K$ ранга 2 (см. §
@sec:l1990-small-central-series, @sec:l1990-small-twisted-rank-two,
@sec:l1990-small-twisted-f4); их исключительность выявилась, в частности, в
[@bib:l1990-small-Levchuk1983, теоремы @th:l1983-rank-four и
@th:l1983-rank-three] и [@bib:l1990-small-Levchuk1987]. Естественным оказалось
рассматривать систему корней типа $F_4$ как объединение систем корней типов
$B_4$ и $C_4$. Отметим, что группы $U G(K)$ ранга 1 над конечным полем
исследуются в [@bib:l1990-small-Suzuki1962; @bib:l1990-small-Ward1966] и др.

=== #[ ] <sec:l1990-small-standard-automorphisms>

Пусть простой корень $q$ и корень $s$ выбраны так, что $q + s$ — максимальный
корень системы корней $Phi$; $c_(s q)$ — структурная константа алгебры Ли типа
$Phi$ относительно базиса Шевалле $e_r (r in Phi), ...$. Отображение
$
  x_q lr((t)) -> x_q lr((t)) x_s lr((d t)) x_(s+q) lr((t^lambda)),
  quad d = c_(s q) (2^lambda - 2(1^lambda))
$ <eq:l1990-small-extremal-automorphism>
(остальные корневые элементы остаются на месте) определяет автоморфизм группы
$U Phi(K)$ для любого преобразования $lambda$ кольца $K$ с условием
$(z+t)^lambda = z^lambda + t^lambda + c_(s q) d z t (z,t in K)$. Если $2K = 0$,
то $d = 0$ и @eq:l1990-small-extremal-automorphism — центральный автоморфизм.
При $2K = K$, с точностью до умножения на центральный автоморфизм, в
@eq:l1990-small-extremal-automorphism можно полагать
$t^lambda = (c_(s q) d t^2 / 2)$, как и в [@bib:l1990-small-Gibbs1970, с. 207];
см. также [@bib:l1990-small-Levchuk1983, § @sec:l1983-automorphism-structure].
Легко выделяются произведения автоморфизмов вида
@eq:l1990-small-extremal-automorphism #source(3, printed: 142)группы $U Phi(K)$,
относительно которых инвариантна подгруппа $U twisted(n, Phi_sigma) lr((K))$,
когда она определена.

Основной результат [@bib:l1990-small-Gibbs1970] для $G != C_n$ заключается в
разложении произвольного автоморфизма группы $U G(K)$ над полем $K = 2K = 3K$ в
произведение стандартного и вида @eq:l1990-small-extremal-automorphism
автоморфизмов. К стандартным автоморфизмам группы $U G(K)$ обычно относят
произведения её внутренних, центральных (т.~е. действующих тождественно по
модулю центра), диагональных, кольцевых и, когда $G = Phi$, графовых
автоморфизмов. Когда $t -> t^(rho(Phi)) (t in K)$ — автоморфизм кольца $K$ для
$rho(Phi) = max lr({(r,r) slash (s,s) | r,s in Phi})$ и группа $U Phi(K)$
допускает графовый автоморфизм порядка 2, скажем $tau$, существенно выделять, по
аналогии с [@bib:l1990-small-Levchuk1983], её идемпотентно-графовый автоморфизм
$
  x_r lr((t)) -> x_r lr((f t^(rho(Phi))))
  [x_r lr((t - f t))]^tau,
  quad t in K, quad r in Phi^+,
$
где $f$ — произвольный идемпотент кольца $K$.

=== #[ ] <sec:l1990-small-central-series>

Пусть, далее, $Gamma_1 = U G(K) supset Gamma_2 supset Gamma_3 supset ...$,
$Z_0 = 1 subset Z_1 subset Z_2 subset ...$ — нижний и соответственно верхний
центральные ряды группы $U G(K)$. Известно, что для группы $U Phi(K)$ при
$(rho(Phi)!) K = K$ они совпадают с её «стандартным» центральным рядом
$U_1 supset U_2 supset ... supset U_h = 1$, где $h$ — число Кокстера системы
корней $Phi$, а $U_i$ — подгруппа, порождаемая корневыми подгруппами
$X_r = x_r lr((K))$ для всевозможных корней $r in Phi$ высоты $>= i$. В общем
случае это не так.

#lemma[
  Для группы $U G_2(K)$ верны равенства:
  $
    Z_1 = U_5 dot x_(2 alpha + beta) lr((cal(Z)_3)),
    quad Z_4 = U_2 dot U G_2 lr((cal(Z)_6)), quad Z_5 = U_1,
  $
  $
    Z_2 = U_4 dot x_(2 alpha + beta) lr((cal(Z)_3)) dot
    lr(
      {x_(alpha + beta) lr((sigma)) x_(2 alpha + beta) lr((sigma)) | sigma in
        A}
    ),
    quad A = Ann_K lr((3 cal(J)_2)),
  $
  $
    Z_3 = U_3 dot x_(alpha + beta) lr((cal(Z)_6)) dot x_beta lr((A)) dot
    lr({x_alpha lr((sigma)) | sigma in A, quad 3(sigma^2-sigma) = 0});
  $
  $
    Gamma_2 = U_5 dot x_(2 alpha + beta) lr((cal(J)_2)) x_(3 alpha + beta)
    lr((3K+cal(J)_3))
    dot lr(
      {x_(alpha + beta) lr((t)) x_(2 alpha + beta) lr((t)) x_(3 alpha +
        beta) lr((-t)) | t in K}
    ),
  $
  $
    Gamma_3 = U_5 dot x_(2 alpha + beta) lr((2K)) dot x_(3 alpha + beta) lr(
      (3
        cal(J)_2)
    ),
  $
  $
    Gamma_4 = x_(3 alpha + 2 beta) lr((3 cal(J)_2)) x_(3 alpha + beta) lr((6K)),
    quad Gamma_5 = x_(3 alpha + 2 beta) lr((6K)), quad Gamma_6 = 1.
  $
  #source(4, printed: 143)Здесь $cal(Z)_t$ — аннулятор элемента $t$ в кольце
  $K$, $cal(J)_m$ — идеал кольца $K$, порождённый множеством
  $lr({t^m - t | t in K})$. В частности, ступень нильпотентности равна 5 при
  $6K != 0$, равна 4 при $6K = 0$, $3 cal(J)_2 != 0$ и равна 3 при
  $3 cal(J)_2 = 0$.
] <lem:l1990-small-g2-central-series>

#proof[
  Установим формулы для членов $Gamma_i$, $Z_i$ при $i <= 3$; когда $i > 3$,
  формулы становятся очевидными. Применяя коммутаторную формулу Шевалле к группе
  $U G_2(K)$, мы будем использовать таблицу структурных констант, выбранную в
  [@bib:l1990-small-Carter1972, с. 211].

  Множества $U_5 dot x_(3 alpha + beta) lr((3K)) = [U_1,U_3]$ и элементы
  $x_(alpha + beta) lr((t)) x_(2 alpha + beta) lr((t)) x_(3 alpha + beta)
  lr((-t)) =
  [x_beta lr((t)), x_alpha lr((1))] mod U_5$ лежат в коммутанте $Gamma_2$. Кроме
  того, коммутант содержит элементы
  $
    x_(2 alpha + beta) lr((sigma(t^2-t))) x_(3 alpha + beta) lr((sigma(t-t^3)))
    =
    [x_beta lr((sigma)), x_alpha lr((t))] [x_beta lr((-sigma t)), x_alpha
      lr((1))] mod U_5.
  $
  Положив $t = -1$, получим включение
  $x_(2 alpha + beta) lr((2K)) subset Gamma_2$. Но тогда коммутант содержит и
  множества $x_(3 alpha + beta) lr((2 cal(J)_3 + 3K)) = x_(3 alpha + beta) lr(
    (cal(J)_3 +
      3K)
  )$, $x_(2 alpha + beta) lr((cal(J)_2))$. Тем самым включение $supset$ в
  формуле для $Gamma_2$ доказано; обратное включение очевидно. Коммутируя
  $X_beta$ с $[x_beta lr((t)),x_alpha lr((1))]$ и
  $x_(2 alpha + beta) lr((cal(J)_2))$ с $x_alpha lr((1))$, устанавливаем
  включение в $Gamma_3$ нормальной подгруппы
  $U_5 dot x_(3 alpha + beta) lr((3 cal(J)_2))$; по её модулю
  $x_(2 alpha + beta) lr((2K)) = [X_alpha,[x_beta lr((1)),x_alpha lr((1))]]$.
  Сейчас формула для $Gamma_3$ очевидна.

  Поскольку $U_1 slash U_3 approx U T(3,K)$, то $Z_1 subset U_2$ и произвольный
  элемент $alpha in Z_1$ по модулю $U_3$ равен $x_(alpha + beta) lr((t))$.
  Коммутируя $alpha$ с элементами $x_(2 alpha + beta) lr((1))$,
  $x_beta lr((1))$, $x_alpha lr((1))$, получаем равенства $3t = 2t = 0$ и
  включение $alpha in U_5 dot x_(2 alpha + beta) lr((cal(Z)_3))$. Отсюда
  вытекает, что $U_5 dot x_(2 alpha + beta) lr((cal(Z)_3))$ есть центр. Как и
  выше, $Z_2 subset U_2$. Конечно, $U_4 Z_1 subset Z_2$. Пусть
  $alpha = x_(alpha + beta) lr((t)) x_(2 alpha + beta) lr((t')) in Z_2$. Тогда
  элементы
  $
    [x_alpha lr((sigma)), alpha] = x_(2 alpha + beta) lr((2 sigma t))
    x_(3 alpha + beta) lr((3 sigma^2 t - 3 sigma t')) mod U_5
  $
  лежат в центре при всех $sigma in K$. Полагая $sigma = 1$, получаем
  $3t' = 3t$, т.~е. $t' in t + cal(Z)_3$. Следовательно, по модулю центра для
  элемента $alpha$ можно считать #source(5, printed: 144)$t' = t$, $t in A$, и
  мы получаем требуемый вид для $Z_2$. Отметим, что
  $
    2K subset cal(J)_2, quad 6K subset 3 cal(J)_2 subset 3K,
    quad cal(Z)_3 subset A = Ann_K lr((3 cal(J)_2)) subset
    cal(Z)_6 = cal(Z)_2 + cal(Z)_3.
  $
  Очевидно, $Z_3 supset Z_2 U_3 = x_(alpha + beta) lr((A)) U_3$,
  $U_1 slash U_4 approx U B_2(K)$. По модулю $Z_2 U_3$ элемент $alpha in Z_3$
  имеет вид $x_alpha lr((t)) x_beta lr((t')) x_(alpha + beta) lr((t''))$, причём
  $
    Z_2 in.rev [alpha,x_alpha lr((sigma))] = x_(alpha + beta) lr((sigma t'))
    x_(2 alpha + beta) lr((sigma^2 t' + 2 sigma t'')) mod U_4, quad sigma in K.
  $
  Следовательно, $t' in A$, $t' sigma^2 in t' sigma + cal(Z)_3$ и
  $2t'' in cal(Z)_3$. Отсюда вытекает включение
  $Z_3 supset x_beta lr((A)) x_(alpha + beta) lr((cal(Z)_6)) U_3$. Поэтому $Z_3$
  содержит элемент $x_alpha lr((t))$. Его коммутатор с $x_beta lr((1))$ лежит в
  $Z_2$ и по модулю $U_4$ равен
  $x_(alpha + beta) lr((t)) x_(2 alpha + beta) lr((t^2))$. Следовательно,
  $t in A$, $t^2 - t in cal(Z)_3$, и мы получаем требуемое равенство для $Z_3$.
  Лемма доказана.
]

#corollary[
  Верхний и нижний центральные ряды группы $U G_2(K)$ над полем $K$ совпадают с
  рядом
  $
    U_1 supset U_2 supset U_3 supset U_4 supset U_5 supset 1
    quad "при" 6K != 0,
  $
  $
    U_1 supset U_2 supset U_4 supset U_5 supset 1
    quad "при" 2K = 0, |K| > 2,
  $
  $
    U_1 supset U_4 lr(⟨x_(alpha + beta) lr((1)) x_(2 alpha + beta) lr((1))⟩)
    supset U_5 supset 1 quad "при" K = "GF"(2),
  $
  $
    U_1 supset U_2 supset U_3 x_(2 alpha + beta) lr((K)) supset 1
    quad "при" 3K = 0.
  $
  Исключением является лишь нижний центральный ряд
  $U_1 supset U_5 x_(2 alpha + beta) lr((K))
  lr(⟨x_(alpha + beta) lr((1)) x_(3 alpha + beta) lr((-1))⟩)
  supset U_5 x_(2 alpha + beta) lr((K)) supset 1$ группы $U G_2(3)$.
] <cor:l1990-small-g2-field-central-series>

#theorem[
  Всякий автоморфизм группы $U G_2(K)$ над полем $K$ характеристики $!= 3$
  разложим в произведение стандартного и вида
  $
    x_beta lr((t)) -> x_beta lr((t)) x_(3 alpha + beta) lr((2d t))
    x_(3 alpha + 2 beta) lr((-d t^2)), quad t in K, quad d in K,
  $ <eq:l1990-small-g2-extremal>
  автоморфизмов и при $K = "GF"(2)$ или $"GF"(4)$ на автоморфизм, который
  порождается автоморфизмом
  $
    x_beta lr((t)) -> x_beta lr((t)) x_(2 alpha + beta) lr((k t)),
    quad x_(alpha + beta) lr((t)) -> x_(alpha + beta) lr((t)) x_(3 alpha + beta)
    lr((k t)), \
    x_(2 alpha + beta) lr((t)) -> x_(2 alpha + beta) lr((t)) x_(3 alpha + 2
    beta) lr((k t^2)),
    quad t in K
  $ <eq:l1990-small-g2-small-field>
  (#source(6, printed: 145)$k in K$ произвольно), и полуграфовым автоморфизмом
  $
    x_alpha lr((t)) -> x_alpha lr((t^2)),
    quad x_(alpha + beta) lr((t)) -> x_(2 alpha + beta) lr((t)),
    quad x_(2 alpha + beta) lr((t)) -> x_(alpha + beta) lr((t)), \
    x_(3 alpha + beta) lr((t)) -> x_(3 alpha + beta) lr((t)) x_(3 alpha + 2
    beta) lr((t^2)).
  $
] <th:l1990-small-g2-non-three>

#proof[
  Исследуем произвольный автоморфизм $phi$ группы $U G_2(K)$. Пусть $|K| > 2$. В
  силу следствия @cor:l1990-small-g2-field-central-series, $U_2$, $U_4$, $U_5$,
  $X_alpha U_2 = C(U_4)$ (централизатор подгруппы $U_4$),
  $X_beta U_2 = C_(mod U_3) lr((U_2))$ (т.~е. наибольшая подгруппа $H$ с
  условием $[H,U_2] subset U_3$) — характеристические подгруппы.

  Если $2K != 0$, то $phi$ индуцирует автоморфизм на фактор-группе
  $U_1 slash U_3 approx U T(3,K)$ и, по теореме @th:l1983-rank-three
  [@bib:l1990-small-Levchuk1983], единичен по модулю $U_2$, с точностью до
  умножения на диагональный и кольцевой автоморфизмы. Умножением на внутренний
  автоморфизм добиваемся тождественности $phi$ на $x_alpha lr((1))$ по модулю
  центра и на $x_beta lr((t))$ по модулю $U_3$. Инвариантность основных
  соотношений показывает, что $phi$ есть произведение автоморфизма
  @eq:l1990-small-g2-extremal на центральный автоморфизм.

  При $2K = 0$ существуют преобразования $lambda_i$, $mu_i$, $0 <= i <= 4$,
  кольца $K$ такие, что
  $
    x_alpha^phi lr((t)) = x_alpha lr((t^(lambda_0)))
    x_(alpha + beta) lr((t^(lambda_1))) x_(2 alpha + beta) lr((t^(lambda_2)))
    ...,
    quad x_beta^phi lr((t)) = x_beta lr((t^(mu_0)))
    x_(alpha + beta) lr((t^(mu_1))) ...,
  $
  $
    [x_alpha lr((s)), [x_alpha lr((t)),x_beta lr((u))],x_beta lr((sigma))]^phi =
    x_(3 alpha + 2 beta) lr(
      {sigma^(mu_0) u^(mu_0)
        [s^(lambda_0) (t^(lambda_0))^2 + (s^(lambda_0))^2 t^(lambda_0)]}
    ).
  $ <eq:l1990-small-g2-fourfold-commutator>

  В силу характеристичности $U_2$, $lambda_0$, $mu_0$ — автоморфизмы аддитивной
  группы $K^+$. Умножением $phi$ на диагональный автоморфизм добиваемся равенств
  $1^(lambda_0) = 1^(mu_0) = 1$. Для фиксированных $s,t in K$ с условием
  $s t^2 != s^2 t$ из @eq:l1990-small-g2-fourfold-commutator следует, что
  $u^(mu_0) sigma^(mu_0) = (u sigma)^(mu_0) 1^(mu_0) (u,sigma in K)$, т.~е.
  $mu_0$ — автоморфизм поля $K$. С точностью до умножения $phi$ на кольцевой
  автоморфизм, $mu_0 = 1$. Поэтому, в силу
  @eq:l1990-small-g2-fourfold-commutator,
  $x_(3 alpha + 2 beta)^phi lr((sigma)) = x_(3 alpha + 2 beta) lr((d sigma))$,
  $sigma in K$, для #source(7, printed: 146)некоторого $d in K$, $d != 0$. При
  этом $(s t^2 + s^2 t)d = s^(lambda_0) (t^(lambda_0))^2 +
  (s^(lambda_0))^2 t^(lambda_0)$, другими словами,
  $
    (t^(lambda_0))^2 = t^(lambda_0) + d(t^2+t),
    quad t^(lambda_0)(s^2+s) = s^(lambda_0)(t^2+t) + s t^2 + s^2 t
    quad (s,t in K).
  $
  Отсюда при некотором $k in K$ получим $t^(lambda_0) = k t^2 + (k+1)t$, причём
  $(t^2+t)[k^2(t^2+t)+k+1+d] = 0$, $t in K$. Следовательно, при $lambda_0 != 1$
  должны иметь $K = "GF"(4)$, $t^(lambda_0) = t^2 (t in K)$, $k = 1 = d$.
  Поэтому умножая, если необходимо, $phi$ на полуграфовый автоморфизм,
  добиваемся тождественности $phi$ по модулю $U_2$ и на $U_5$.

  Умножая $phi$ на внутренний автоморфизм, добиваемся равенств
  $1^(mu_4) = 1^(lambda_1) = 1^(lambda_3) = 0$. Тогда соотношения
  $
    x_(3 alpha + beta)^phi lr({u(s t^2 + s^2 t)}) =
    [x_alpha lr((s)), [x_alpha lr((t)), x_beta lr((u))]]^phi dot
    x_(3 alpha + 2 beta) lr((s t^2 u^2)) = \
    = x_(3 alpha + beta) lr((u(s t^2 + s^2 t)))
    x_(3 alpha + 2 beta) lr(((s^(lambda_1) t^2 + s^(lambda_2) t)u)),
    quad u,s,t in K,
  $
  при $s = t = 1$ и при $s = 1$ дают равенства $1^(lambda_2) = 0$,
  $s^(lambda_1) t^2 = s^(lambda_2) t$, $s,t in K$. Отсюда $lambda_1 = lambda_2$,
  $s^(lambda_1)(t^2+t) = 0$ и $lambda_1 = lambda_2 = 0$. Следовательно, $phi$
  единичен на $U_4$. Из перестановочности элемента $x_beta^phi lr((s))$ с
  элементом
  $
    x_(alpha + beta)^phi lr((u t)) x_(2 alpha + beta)^phi lr((u t^2)) =
    [x_alpha^phi lr((t)),x_beta^phi lr((u))] x_(3 alpha + beta) lr((u t^3)) =
    x_(alpha + beta) lr((u t)) times \
    x_(2 alpha + beta) lr((u t^2)) x_(3 alpha + beta) lr(
      (u^(mu_1)t^2 +
        u^(mu_2)t)
    )
    mod U_5, quad s,t,u in K,
  $
  следует, что $(s u^(mu_1) + s^(mu_1)u)t^2 =
  (s u^(mu_2) + s^(mu_2)u)t$. Когда $s = t = 1$, отсюда находим
  $u^(mu_1) = u^(mu_2) + 1^(mu_2)u$. Следовательно,
  $(s u^(mu_2) + s^(mu_2)u)(t^2+t) = 0$, $u^(mu_2) = 1^(mu_2)u$, $mu_1 = 0$.
  Изоморфизм $X_beta approx K^+$ даёт
  $(z+t)^(mu_4) = z^(mu_4) + t^(mu_4) + z t^(mu_3)$, откуда $1^(mu_3) = 0$,
  $t^(mu_3) = 1^(mu_3)t = 0$, т.~е. $mu_3 = 0$.

  Далее, умножив элемент
  $x_(alpha + beta)^phi lr((u t)) x_(2 alpha + beta)^phi lr((u t^2))$ на
  элемент, полученный заменой $(u,t) -> (u t,1)$, находим
  #source(8, printed: 147)
  $
    x_(2 alpha + beta)^phi lr([u(t^2+t)]) = x_(2 alpha + beta) lr([u(t^2+t)])
    x_(3 alpha + 2 beta) lr([u t^(lambda_3) + u^2(t^2+t)1^(mu_2)]).
  $
  Последняя координата здесь, очевидно, имеет вид $k sigma^2 + m sigma$, где
  $k,m$ — фиксированные элементы из $K$, $sigma = u(t^2+t)$. Поэтому
  $
    t^(lambda_3) = (m+1^(mu_2))(t^2+t)+k(t^2+t)^2,
    quad (u+u^2)[k(t^2+t)^2+1^(mu_2)(t^2+t)] = 0 quad (u,t in K).
  $
  Отсюда $k = 1^(mu_2)$ и либо $K = "GF"(4)$, либо $k = 0$. В обоих случаях
  $t^(lambda_3) = m(t^2+t)$ и $phi$ есть произведение центрального автоморфизма,
  сопряжения элементом $x_(alpha + beta) lr((m)) x_(2 alpha + beta) lr((m))$ и
  автоморфизма @eq:l1990-small-g2-small-field.

  Пусть $phi in Aut U G_2(2)$. Образы корневых элементов $x_r lr((1)) = x_r$
  есть инволюции. Поэтому автоморфизм $phi$, с точностью до умножения на
  автоморфизм @eq:l1990-small-g2-small-field, по модулю коммутанта (см.
  следствие @cor:l1990-small-g2-field-central-series) индуцирует подстановку на
  множестве $x_alpha$, $x_beta$, $x_(alpha + beta)$. Несложно убедиться, что
  подстановка единична и умножением на внутренний и центральный автоморфизмы
  $phi$ приводится к 1 или к полуграфовому автоморфизму. Теорема доказана.
]

Пусть $K$ — поле характеристики 3, $|K| > 3$, и $mu$ — эндоморфизм его
аддитивной группы с условием
$
  lr(((sigma c^3)/(c-c^3)))^mu - lr((sigma/(c-c^3)))^mu c = \
  = lr(((sigma t^3)/(t-t^3)))^mu - lr((sigma/(t-t^3)))^mu t = sigma^psi,
  quad c^3 != c, quad t^3 != t,
$ <eq:l1990-small-g2-additive-condition>
$c,t,sigma in K$. Нетрудно убедиться, что для любых $f,d in K$ отображение
$
  cases(
    reverse: #true,
    x_alpha lr((t)) -> x_alpha lr((t)) x_(3 alpha + beta) lr((f t - d t^3))\,
    quad x_(alpha + beta) lr((t)) -> x_(alpha + beta) lr((t)) x_(2 alpha + beta)
    lr((t^psi))
    x_(3 alpha + 2 beta) lr((f t))\,,
    x_beta lr((t)) -> x_beta lr((t)) x_(alpha + beta) lr((t^mu))\,
    quad x_(3 alpha + beta) lr((t)) -> x_(3 alpha + beta) lr((t)) x_(2 alpha +
    beta) lr((t^(mu+psi)))
    x_(3 alpha + 2 beta) lr((d t)),
  )
$ <eq:l1990-small-g2-characteristic-three-map>
определяет автоморфизм группы $U G_2(K)$. Конечно, когда $mu = psi = 0$,
отображение @eq:l1990-small-g2-characteristic-three-map есть автоморфизм и при
$K = "GF"(3)$.

#theorem[
  Всякий автоморфизм группы $U G_2(K)$ над совершенным полем $K$ характеристики
  3 разложим в произведение стандартного и вида @eq:l1990-small-g2-extremal
  автоморфизмов #source(9, printed: 148)и автоморфизма
  @eq:l1990-small-g2-characteristic-three-map, где $mu in End K^+$ удовлетворяет
  условию @eq:l1990-small-g2-additive-condition при $|K| > 3$ и $mu = psi = 0$
  при $K = GF(3)$. (Если $psi = 0$, то, в силу
  @eq:l1990-small-g2-additive-condition, $t^mu = m root(3, t), t in K$, для
  фиксированного $m in K$; пример $mu$ с ненулевым $psi$ автору неизвестен.)
] <th:l1990-small-g2-characteristic-three>
