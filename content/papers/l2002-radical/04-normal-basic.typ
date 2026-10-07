#import "defs.typ": *

=== Нормальные подгруппы присоединенной группы
<sec:l2002-radical-normal-subgroups>

Основным результатом параграфа является

#theorem[
  Пусть $J$ — нильпотентный сильно максимальный идеал кольца $K$ со свойством
  $2I = I$ для любого идеала $I subset.eq J$ кольца $K$. Если $H$ — произвольная
  нормальная подгруппа присоединенной группы кольца $R_n lr((K, J))$, $n >= 2$,
  и $T$ — ее $(n, 1)$-проекция, то существует и единственна нормальная
  $T$-граница $A = A_N lr((T; Lc, Lc'))$ кольца $R_n lr((K, J))$, нормальное
  замыкание которой совпадает с $H$, причем $A = H inter (tilde(B) + D)$.
] <th:l2002-radical-normal-boundary>

Вначале выпишем стандартные соотношения между элементарными матрицами в
присоединенной группе кольца $R_n lr((K, J))$, используя для коммутатора обычное
обозначение $[a, b] = a' compose b' compose a compose b$:
$
  (x e_(i i))' = x' e_(i i), quad (x e_(i j))' = -x e_(i j), quad i != j;
$
$
  [x e_(i i), y e_(j j)] = [x e_(i j), y e_(k t)] = 0,
  quad j != k comma t != i;
$
$
  [x e_(i j), y e_(j t)] = x y e_(i t), quad i != j comma t != i.
$

Всюду в этом параграфе кольцо $R = R_n lr((K, J))$ радикально. Конечно, это
условие выполняется при условии нильпотентности идеала $J$. Через
$P_(i j) lr((F))$ (аналогично $Q_(i j) lr((F))$) при $F subset K$ здесь в
отличие от §~@sec:l2002-radical-lie-ideals будем обозначать подгруппу
присоединенной группы кольца $R$, порожденную множествами $F e_(k m)$ ($k != m$)
при $(k, m) ≽ (i, j)$ (соответственно $(k, m) ≻ (i, j)$) и еще, когда $i < j$,
множествами ${x e_(k k) + x' e_(m m) | x in F}$ ($i <= k < m <= j$). Ясно, что
$P_(i i) lr((F)) = Q_(i i) lr((F))$.

Зафиксируем нормальную подгруппу $H$ присоединенной группы кольца $R$.

#lemma[
  #source(11, printed: 429)Для всякого идеала $F$ кольца $K$ при
  $H supset F e_(k m)$, $k != m$, выполняется включение
  $H supset P_(k m) lr((F))$, причем при $k < m$ дополнительно предполагается
  $2F = F$. Кроме того, если $k > m$ и $H_(k m)$ — идеал, то
  $P_(k m) lr((H_(k m))) supset H inter P_(k m) lr((K))$.
] <lem:l2002-radical-normal-elementary-closure>

#proof[
  Последнее утверждение леммы вытекает почти непосредственно из
  леммы~@lem:l2002-radical-niltriangular-normal-lie. Докажем первое утверждение.

  Известно (см., например, @bib:l2002-radical-Levchuk1992b), что произвольную
  матрицу $alpha in R_n lr((K, J))$ можно представить, причем единственным
  способом, в виде $alpha = beta compose delta compose gamma$, где
  $beta in sum_(i>j) K e_(i j)$, $delta in sum_(i=1)^n J e_(i i)$ и
  $gamma in sum_(i<j) J e_(i j)$. Установим соответствующее разложение для
  коммутатора $[x e_(k m), y e_(m k)]$. Согласно его определению имеем
  $
    [x e_(k m), y e_(m k)] = (x^2 y^2 + x y)e_(k k) - x y e_(m m)
    + x^2 y e_(k m) - x y^2 e_(m k), quad x in K, y in J.
  $
  Легко проверяется равенство
  $
    [x e_(k m), y e_(m k)] = x t' e_(k m) compose t e_(m m)
    compose t' e_(k k) compose (-y t') e_(m k), quad t = -x y.
  $ <eq:l2002-radical-elementary-commutator-factorization>
  Используя @eq:l2002-radical-elementary-commutator-factorization, получаем
  $
    H supset [e_(v u), F e_(u v)]
    = {t' e_(v u) compose t e_(u u) compose t' e_(v v)
      compose t t' e_(u v) | t = -y in F}, quad k <= u < v <= m.
  $
  Учитывая, что $H supset [F e_(k m), e_(m v)] = F e_(k v)$ при всех $v < m$,
  $v != k$ и $H supset [e_(u k), F e_(k m)] = F e_(u m)$ при всех $u > k$,
  $u != m$, имеем
  $H supset {t' e_(v u) compose t e_(u u) compose t' e_(v v) | t in F}$ и
  $
    H ∋ [x e_(v u), t' e_(v u) compose t e_(u u) compose t' e_(v v)]
    = x(t compose t)e_(v u) = x t(2 + t)e_(v u), quad t in F comma x in K.
  $
  Так как $F subset J$ и $2F = F$ при $k < m$, то $H supset F e_(v u)$.
  Действительно, для любого $z in F$ найдутся $s, r in F$ такие, что $z = 2s$ и
  $s = 2r$. Элемент $1 + r$ обратим, а $(1 + r)^(-1)s(2 + s) = 2s = z$. Отсюда
  $H supset {t e_(u u) compose t' e_(v v) | t in F}$. Кроме того,
  $H supset F e_(u v)$ для всех $(u, v) ≻ (k, m)$, $u != v$, и поэтому
  $H supset P_(k m) lr((F))$. Лемма доказана.
]

Вычислим коммутатор произвольной матрицы $alpha = lr(‖a_(s t)‖) in R$ с
элементарной матрицей $x e_(k m) in R$. Полагая $alpha' = lr(‖a^*_(s t)‖)$,
прямыми вычислениями находим
$
  [x e_(k m), alpha] = x sum_(u != k) sum_(v != m) a^*_(u k) a_(m v)e_(u v)
  + x(1 + a_(m m))sum_(u != k) a^*_(u k)e_(u m)
  + x(1 + a^*_(k k) - x a^*_(m k))sum_(v != m) a_(m v)e_(k v)
  + x(a_(m m) compose a^*_(k k) - x a^*_(m k)(1 + a_(m m)))e_(k m);
$ <eq:l2002-radical-offdiagonal-commutator>
$
  [x e_(k k), alpha] = x sum_(u != k) sum_(v != k) a^*_(u k) a_(k v)e_(u v)
  + x(1 + a_(k k))sum_(u != k) a^*_(u k)e_(u k)
  - x'(1 + a^*_(k k))sum_(v != k) a_(k v)e_(k v)
  - x'(a^*_(k k) compose a_(k k))e_(k k).
$ <eq:l2002-radical-diagonal-commutator>

#lemma[
  Пусть $alpha = lr(‖a_(s t)‖) in H$ и $x e_(k m) in R$, $k != m$. Если
  $beta = [x e_(k m), alpha] = lr(‖b_(s t)‖)$, то в $H$ существует матрица
  $overline(beta) = lr(‖overline(b)_(s t)‖)$ с такими же, как у $beta$,
  недиагональными элементами $m$-го столбца и нулями в остальных столбцах, быть
  может, исключая их элементы в $k$-й и $m$-й строках. А именно, полагая
  $lambda_i = a_(m i)(1 + a_(m m))^(-1)$ при $1 <= i <= n$, $i != m$, матрицу
  $overline(beta)$ можно задать по правилу
  $
    overline(b)_(s t) = cases(
      b_(s t) comma & s != m comma t = m,
      -x^2 a^*_(m k) a_(m k) - lambda_k x comma & (s comma t) = (m comma m),
      lambda_t x comma & s = k comma t != m,
      lambda_k lambda_t x comma & s = m comma t != m,
      0 comma & s != k comma m comma t != m
    ).
  $
] <lem:l2002-radical-normal-column-reduction>

#proof[
  #source(12, printed: 430)Пусть $beta = [x e_(k m), alpha]$ и $lambda_t$
  выбраны, как в лемме~@lem:l2002-radical-normal-column-reduction. Зафиксируем
  $t != m$ и рассмотрим сопряженную с $beta$ матрицу
  $
    gamma = (lambda_t e_(m t)) compose beta compose (-lambda_t e_(m t))
    = beta + lambda_t sum_(v != t) b_(t v)e_(m v)
    - lambda_t sum_(u != t) b_(u m)e_(u t) - lambda_t^2 b_(t m)e_(m t).
  $
  Она отличается от $beta$ самое большее элементами $m$-й строки и $t$-го
  столбца, причем
  $
    pi_(m t) lr((gamma)) = b_(m t) + lambda_t lr((b_(t t) - b_(m m)))
    - lambda_t^2 b_(t m), quad
    pi_(m v) lr((gamma)) = b_(m v) + lambda_t b_(t v) quad (v != t).
  $
  В силу выбора $lambda_t$ и @eq:l2002-radical-offdiagonal-commutator все
  элементы $t$-го столбца матрицы $gamma$ нулевые, исключая, быть может, $k$-й и
  $m$-й. Оставшиеся его элементы также восстанавливаются явно, причем
  $pi_(k t) lr((gamma)) = b_(k t) - lambda_t b_(k m) = lambda_t x$.

  К построенной сопряженной матрице будем применять повторно аналогичные
  сопряжения элементарными матрицами, меняя $t$. Более точно, построим матрицы
  $beta = beta^((0)), beta^((1)), dots, beta^((n))$ рекуррентно по правилу
  $
    beta^((i)) = cases(
      lambda_i e_(m i) compose beta^((i-1)) compose (-lambda_i e_(m i)) comma
      & 1 <= i <= n comma i ∉ {k comma m},
      beta^((i-1)) comma & i in {k comma m}
    ).
  $
  Ясно, что матрица $beta^((n))$ может иметь ненулевые элементы лишь в строках и
  столбцах с номерами $k$ или $m$; как показано выше, все эти элементы
  восстанавливаются явно. Несложно убедиться, что матрица
  $overline(beta) = lambda_k e_(m k) compose beta^((n))
  compose (-lambda_k e_(m k))$ удовлетворяет всем требованиям
  леммы~@lem:l2002-radical-normal-column-reduction. Лемма доказана.
]

С использованием аналога @eq:l2002-radical-offdiagonal-commutator для
коммутатора $[alpha, x e_(k m)]$ аналогично доказывается

#lemma[
  Пусть $alpha = lr(‖a_(s t)‖) in H$ и $x e_(k m) in R$, $k != m$. Если
  $beta = [alpha, x e_(k m)] = lr(‖b_(s t)‖)$, то в $H$ существует матрица
  $overline(beta) = lr(‖overline(b)_(s t)‖) in H$ с такими же, как у $beta$,
  недиагональными элементами $k$-й строки и нулями в остальных строках, быть
  может, исключая их элементы в $k$-м и $m$-м столбцах. Более точно, если
  $lambda_i = -a^*_(i k)(1 + a^*_(k k))^(-1)$, $1 <= i <= n$, $i != k$, то
  матрицу $overline(beta)$ можно задать по правилу
  $
    overline(b)_(s t) = cases(
      b_(s t) comma & s = k comma t != k,
      -x^2 a^*_(m k) a_(m k) - lambda_m x comma & (s comma t) = (k comma k),
      lambda_s x comma & s != k comma t = m,
      -lambda_m lambda_s x comma & s != k comma t = k,
      0 comma & s != k comma t != k comma m
    ).
  $
] <lem:l2002-radical-normal-row-reduction>

#lemma[
  Пусть $alpha = lr(‖a_(s t)‖) in H$, $v != m$ и $u != k$. Тогда
  #letter-list(
    [если $k > m$, то $K a_(m v) subset H_(k v)$ и $K a_(u k) subset H_(u m)$;],
    [$J a_(m v) subset H_(k v)$ и $J a_(u k) subset H_(u m)$.],
  )
] <lem:l2002-radical-normal-projections>

#proof[
  При всех $x in K$ из @eq:l2002-radical-offdiagonal-commutator получаем
  включения $x a^*_(u k)(1 + a_(m m)) in H_(u m)$ ($u != k$) и
  $x(1 + a^*_(k k) - x a^*_(m k))a_(m v) in H_(k v)$ ($v != m$). Учитывая
  обратимость элементов $1 + a_(m m)$ и $1 + a^*_(k k) - x a^*_(m k)$, получаем
  требуемые в (а) включения.

  Случай (б) рассматривается аналогично при $k != m$, а при $k = m$ достаточно
  заметить, что в силу @eq:l2002-radical-diagonal-commutator
  $
    J(1 + a^*_(k k))a_(k v) = J a_(k v) subset H_(k v) quad (v != k),
    quad J(1 + a_(k k))a^*_(u k) = J a_(u k) subset H_(u k) quad (u != k).
  $
  Остается воспользоваться произволом $alpha$ в $H$. Лемма доказана.
]
