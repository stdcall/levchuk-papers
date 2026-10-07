#import "defs.typ": *

#lemma[
  #source(13, printed: 431)Пусть $(k, m) ≺ (u, v)$ и $k != m$. Если $2I = I$ для
  любого идеала $I subset J$ кольца $K$, то $H_(u v)$ содержит идеал,
  порожденный проекцией $H_(k m)$ в $K$.
] <lem:l2002-radical-normal-projection-ideal>

#proof[
  Вначале докажем включение $K a_(k m) subset H_(u v)$ для произвольной матрицы
  $alpha = lr(‖a_(s t)‖) in H$. В силу леммы
  @lem:l2002-radical-normal-projections (а) достаточно рассмотреть случай, когда
  $m = k + 1$ и $(u, v) = (k + 1, k)$. Пусть $x in K$ и
  $beta = [alpha, x e_(k+1,k)]$. Тогда $H$ содержит матрицу $overline(beta)$,
  коэффициенты которой определяются по лемме
  @lem:l2002-radical-normal-row-reduction. Следовательно, $H$ содержит матрицу
  $[e_(k+1,k), overline(beta)]$ с $(k + 1, k)$-проекцией
  $x lambda_k lr((2 + d))$, где
  $lambda_k = -a^*_(k,k+1)(a^*_(k+1,k+1) + 1)^(-1)$ и
  $d = lambda_k + x lambda_k + x lambda_k^2$. По условию
  $2K a_(k,k+1) = K a_(k,k+1)$ и, в частности, существует элемент
  $c in K a^*_(k,k+1)$ такой, что
  $
    d = 2c, quad K lambda_k lr((2 + d)) = 2K lambda_k lr((1 + c))
    = 2K lambda_k = K lambda_k = K a^*_(k,k+1).
  $
  Учитывая произвол в выборе $alpha in H$, получаем включение
  $K a_(k,k+1) subset H_(k+1,k)$ и, следовательно, включение
  $K a_(k m) subset H_(u v)$ доказано.

  Если $v < m$, то $H supset [K e_(m v), alpha']$ и в силу равенств
  $pi_(k v) lr([K e_(m v), alpha']) = K a_(k m)(1 + a^*_(v v)) = K a_(k m)$
  должны иметь $pi_(k v) lr(([K e_(m v), alpha'])) = K a_(k m)$. Отсюда для
  любого конечного семейства матриц $alpha_i = lr(‖a_(s t)^((i))‖) in H$ прямыми
  вычислениями находим
  $
    pi_(k v) lr(
      ([K e_(m v), alpha'_1] compose dots compose
        [K e_(m v), alpha'_s])
    ) = K a_(k m)^((1)) + dots + K a_(k m)^((s)).
  $
  Поэтому проекция $H_(k v)$ содержит идеал, порожденный $H_(k m)$ в $K$.
  Аналогично $K H_(k m) subset H_(u m)$, $u > k$. Комбинируя полученные
  включения, получаем утверждение леммы для всех $(k, m) ≺ (u, v)$, исключая
  случай, когда $m = k + 1$ и $(u, v) = (k + 1, k)$. То же самое включение в
  исключительном случае получаем, используя дополнительно соотношения
  $pi_(k+1,k) lr(([e_(k+1,k), [K e_(k+1,k), alpha']])) = K a_(k,k+1)$. Лемма
  доказана.
]

Как следствие должны иметь $K H_(u v) subset H_(n 1)$ для всех
$(u, v) != (n, 1)$, $u != v$. Доказанная лемма показывает, что определение
множеств $Lc(H)$ и $Lc'(H)$ после леммы @lem:l2002-radical-lie-projections в
§~@sec:l2002-radical-lie-ideals дословно переносится и на случай нормальной
подгруппы $H$ присоединенной группы. Когда $J$ — сильно максимальный идеал,
легко переносится и лемма @lem:l2002-radical-lie-corner-classification вместе с
доказательством. С учетом леммы~@lem:l2002-radical-normal-projection-ideal
получается

#lemma[
  Пусть $Lc = Lc(H)$, $Lc' = Lc'(H)$ и $T = H_(n 1)$. Тогда $Lc$, $Lc'$ —
  множество углов степени $n$, и если $Lc(H) != {(n, 1)}$, то $T$ — идеал кольца
  $K$. Если $J$ — сильно максимальный идеал кольца $K$, то при
  $(k, m) ∉ Lc union Lc'$, $k != m$, имеем либо $(k, m) ≻ Lc$ и $H_(k m) = T$,
  либо $(k, m) ≻ Lc'$, $(k, m) ⊁ Lc$ и $H_(k m) = J T$, либо $(k, m) ⊁ Lc'$ и
  $H_(k m) = J^2 T$.
] <lem:l2002-radical-normal-corner-classification>

#lemma[
  Пусть $F$ — идеал кольца $K$, $alpha = lr(‖a_(s t)‖) in H$ и
  $H supset P_(k m) lr((F))$, $k != m$. Тогда найдется матрица
  $beta = lr(‖b_(s t)‖) in H$ такая, что $det(beta + e) = det(alpha + e)$ и
  #letter-list(
    [$b_(u v) = a_(u v)$ при $u < k$, и $b_(u v) = a_(u v) mod J F$ при
      $u >= k$, $v > m$;],
    [если $(u, v) ≽ (k, m)$ и $a_(u v) ∉ F$, то $b_(u v) = a_(u v) mod J F$;],
    [если $(u, v) ≽ (k, m)$ и $a_(u v) in F$, то $b_(u v) = 0 mod J F$,
      исключая, быть может, фиксированную (произвольно) позицию $(t, t)$ с
      условием $k <= t <= m$.],
  )
] <lem:l2002-radical-normal-elimination>

#proof[
  Покажем, что требуемую матрицу $beta$ можно найти, умножая матрицу
  $alpha in H$ на элементарные матрицы из $P_(k m) lr((F))$. Вначале преобразуем
  в $alpha$ коэффициенты $a_(u v)$ при $(u, v) ≽ (k, m)$, $u != v$. Произведение
  $x e_(u v) compose alpha = x e_(u v) + alpha + x sum_j a_(v j)e_(u j)$
  имеет $(u, v)$-проекцию $x(1 + a_(v v)) + a_(u v)$. Поэтому при $a_(u v) in F$
  существует $x in F$, при котором произведение лежит в $H$, а его
  $(u, v)$-проекция равна нулю. Ясно, что определитель матрицы $alpha + e$ не
  изменился. Элементы матрицы $alpha$, расположенные выше $u$-й строки, не
  изменились, а #source(14, printed: 432)расположенные правее $v$-го столбца, не
  изменились по модулю $J F$. Аналогично умножаем $alpha$ на элементарные
  матрицы $x e_(u v)$ при $a_(u v) in F$ и $u >= k$ последовательно для
  $v = m, m - 1, dots, 1$. Получаем матрицу, у которой все элементы
  удовлетворяют условиям леммы, исключая, быть может, элементы на позициях
  $(t, t)$, $k <= t <= m$.

  Зафиксируем указанное $t$ при $k < m$, и пусть $a_(v v) in F$, $k <= v <= m$,
  $v != t$. Положим $x = a'_(v v)$. Тогда матрица
  $
    H ∋ x' e_(t t) compose x e_(v v) compose alpha
    = x' e_(t t) + x e_(v v) + alpha
    + x' sum_j a_(t j)e_(t j) + x sum_j a_(v j)e_(v j)
  $
  лежит в $H$. По модулю $J F$ она совпадает с $x' e_(t t) + x e_(v v) + alpha$,
  а ее $(v, v)$-проекция равна нулю. Кроме того, проведенное преобразование не
  изменяет элементов выше $k$-й строки. В силу произвола в выборе $v$ лемма
  доказана.
]

#lemma[
  Если $J$ — нильпотентный идеал и $2I = I$ для любого идеала $I subset.eq J$
  кольца $K$, то $H supset P_(1 n) lr((J^2 T))$.
  #ed-note[В оригинале указана только нильпотентность $J$. Этого недостаточно:
    при $K = ZZ/(8 ZZ)$, $J = 2K$ нормальное замыкание $e_(2 1)$ имеет
    $(2, 1)$-проекцию $T = K$, но не содержит $4e_(1 2)$.]
] <lem:l2002-radical-normal-jjt>

#proof[
  Положим $F_r = J^r T$, $r >= 2$, и выберем $m$ так, что $J^m = 0$. Все $F_r$ —
  идеалы кольца $K$, содержащиеся в $J$, так что $2F_r = F_r$, $J F_r = F_(r+1)$
  и $F_r^2 subset F_(r+1)$. Здесь, как и в определении произведения $J^r T$,
  берутся конечные суммы произведений элементов соответствующих множеств.

  Пусть $alpha = lr(‖a_(s t)‖) in H$, $x, y in J$ и $beta = [x e_(1 n), alpha]$.
  Выберем $overline(beta) in H$ по
  лемме~@lem:l2002-radical-normal-column-reduction и положим
  $lambda = a_(n 1)(1 + a_(n n))^(-1)$,
  $gamma = lr(‖c_(s t)‖) = [y e_(1 n), overline(beta)']$. Прямое вычисление по
  @eq:l2002-radical-offdiagonal-commutator дает
  $
    c_(1 n) = x y lambda lr((2 + (x-y)lambda - x y lambda^2)),
    quad c_(n n) = x y lambda^2(1 + x lambda).
  $
  Все коэффициенты $gamma$ лежат в $F_2$, ее строки с номерами $2, dots, n-1$
  нулевые, а недиагональные коэффициенты последней строки лежат в $F_3$. Кроме
  того, $det(e + gamma) = 1$ и $c_(1 n) = 2x y a_(n 1) mod F_3$. Если $C$ —
  идеал, порожденный всеми такими $c_(1 n)$, то $F_2 = C + J F_2$: образы
  $2x y a_(n 1)$ порождают $F_2/F_3$. Последовательно подставляя это равенство в
  правую часть и пользуясь $J^m = 0$, получаем $C = F_2$.

  При $n > 2$ для любого $u in K$ коммутаторы
  $
    [u e_(n,n-1), gamma']
    = u c_(n n)e_(n,n-1) compose u c_(1 n)e_(1,n-1),
  $
  $
    [u c_(n n)e_(n,n-1) compose u c_(1 n)e_(1,n-1), e_(n 1)]
    = -u c_(1 n)e_(n,n-1)
  $
  лежат в $H$. Поэтому $F_2 e_(n,n-1) subset H$. Удаляя из первого коммутатора
  уже полученный нижний элемент и беря конечные произведения, находим
  $F_2 e_(1,n-1) subset H$. Аналогичным вычислением с транспонированием
  относительно побочной диагонали получаем $F_2 e_(2 n) subset H$.
  Лемма~@lem:l2002-radical-normal-elementary-closure дает
  $Q_(1 n) lr((F_2)) subset H$.

  Теперь проводим убывающую индукцию по $r$ от $r = m$ до $r = 2$. Предположим,
  что $F_(r+1)e_(1 n) subset H$, и повторим построение $gamma$ с $x in J$,
  $y in J^(r-1)$. Ее коэффициенты лежат в $F_r$, определитель $e+gamma$ равен
  единице, а $(1,n)$-коэффициент равен $2x y a_(n 1)$ по модулю $F_(r+1)$.
  Умножением на элементы $Q_(1 n) lr((F_r)) subset H$ удаляем остальные
  недиагональные и диагональные коэффициенты. Это обычное исключение с
  обратимыми ведущими элементами $1+f$, $f in F_r$; определитель обеспечивает
  удаление последнего диагонального коэффициента. Полученный чистый
  $(1,n)$-элемент по модулю $F_(r+1)$ имеет прежний коэффициент, поскольку все
  поправки лежат в $F_r^2 subset F_(r+1)$. Эти коэффициенты аддитивно порождают
  $F_r/F_(r+1)$ в силу $2F_r = F_r$. Конечные произведения чистых
  $(1,n)$-элементов и индуктивное предположение дают $F_r e_(1 n) subset H$. При
  $r=2$ заключаем по лемме~@lem:l2002-radical-normal-elementary-closure, что
  $P_(1 n) lr((F_2)) subset H$.

  Пусть $n = 2$. При $F_2 = 0$ утверждение тривиально. В остальных случаях
  положим $M_0 = {gamma | x,y in J, alpha in H}$ и для $s >= 1$ обозначим через
  $M_s$ множество последовательных коммутаторов
  $[[dots [gamma, z_1 e_11], dots], z_s e_11]$, где $z_i in J$. По
  @eq:l2002-radical-diagonal-commutator их верхние и диагональные коэффициенты
  лежат в $F_(s+2)$, а нижние — в $F_(s+3)$. По модулю $F_(s+3)$ верхние
  коэффициенты имеют вид $2x y a_(2 1) z'_1 dots z'_s$. Поскольку
  $z -> z' = -z(1+z)^(-1)$ переставляет $J$, эти коэффициенты аддитивно
  порождают $F_(s+2)/F_(s+3)$.

  Вновь проводим убывающую индукцию, начиная с
  $P_(1 2) lr((F_m)) = {0} subset H$. Пусть $3 <= t <= m$ и
  $P_(1 2) lr((F_t)) subset H$. Обозначим $F = F_(t-1)$, $E = e_(2 1)$. По
  модулю $F_t$ любая матрица $A in M_(t-3)$ имеет вид
  $
    A = mat(d, c; 0, -d), quad d,c in F,
  $
  так как $det(e+A)=1$ и $F^2 subset F_t$. В этом слое прямое вычисление
  коммутаторов дает для $u in K$
  $
    [u E,A] = mat(-u c, 0; 2u d+u^2 c, u c),
    quad [E,[u E,A]] = -2u c E mod F_t.
  $
  Коэффициенты $c$ аддитивно порождают $F/F_t$, а $2F=F$. Поэтому двойные
  коммутаторы и уже известное включение $F_t E subset H$ дают $F E subset H$. Из
  первых коммутаторов удаляем нижние элементы и получаем все парные диагональные
  элементы $d e_11 + d' e_22$, $d in F$, по модулю $F_t$. Из матриц $M_(t-3)$
  затем удаляем эти диагональные элементы и получаем $F e_12 subset H$ по модулю
  $F_t$. Здесь переход от коэффициентных сравнений к включениям допустим: всякая
  матрица определителя 1, совпадающая с $e$ по модулю $F_t$, лежит в
  $e + P_(1 2) lr((F_t))$ по элементарному исключению. Конечные произведения и
  $P_(1 2) lr((F_t)) subset H$ поэтому устраняют все остатки. По
  лемме~@lem:l2002-radical-normal-elementary-closure $P_(1 2) lr((F)) subset H$.
  При $t=3$ получаем требуемое включение $P_(1 2) lr((J^2 T)) subset H$. Лемма
  доказана.
]

Далее предполагаем, что $J$ — нильпотентный сильно максимальный идеал, причем
$2I = I$ для любого идеала $I subset J$ кольца $K$.

#lemma[
  Пусть $M subset H inter (P_(k m) lr((J T)) + P_(1 n) lr((J^2 T)))$ и
  $M_(k m) = J T$ для фиксированной позиции $(k, m)$, $k != m$, причем
  $det(alpha + e) = 1$ для всех $alpha in M$. Тогда
  $H supset P_(k m) lr((J T))$.
] <lem:l2002-radical-normal-jt-closure>

#proof[
  По лемме~@lem:l2002-radical-normal-jjt $H supset P_(1 n) lr((J^2 T))$, так что
  достаточно рассмотреть случай, когда $M subset H inter P_(k m) lr((J T))$ и
  $M_(k m) = J T$. При $k > m$ требуемое в лемме включение вытекает сейчас
  непосредственно из последнего утверждения
  леммы~@lem:l2002-radical-normal-elementary-closure. Если $m = k + 1$, то
  пересечение $H inter NT_n lr((K))$ содержит множества
  $
    [e_(k+1,k), [K e_(k+1,k), M]], quad
    [e_(k,k-1), [K e_(k+1,k), M]], quad
    [e_(k+2,k+1), [K e_(k+1,k), M]]
  $
  #source(15, printed: 433)и по доказанному множества $P_(k+1,k) lr((J T))$,
  $P_(k,k-1) lr((J T))$ и $P_(k+2,k+1) lr((J T))$ соответственно. Учитывая также
  соотношение $H supset [K e_(k+1,k), M]$, как и выше, находим
  $H supset P_(k,k+1) lr((J T))$.

  Далее проводим индукцию по $m - k$. Выберем для каждой матрицы $alpha in M$
  матрицу $beta = beta_alpha in H$ так, как указано в
  лемме~@lem:l2002-radical-normal-elimination при $F = J^2 T$. Все
  $(u, v)$-проекции множества $beta_M$ лежат в $J T$ при $(u, v) ≽ (k, m)$,
  исключая, быть может, случай $(u, v) = (t, t)$ для фиксированного $t$, а в
  остальных случаях они лежат в $J^3 T$. Кроме того, $(k, m)$-проекция множества
  $beta_M$ равна $J T$ по построению. Далее применяем
  лемму~@lem:l2002-radical-normal-elimination к матрицам из множества $beta_M$
  при $F = J^3 T$, и т. д. В силу нильпотентности идеала $J$ через конечное
  число шагов найдем множество
  $M' subset (P_(k m) lr((J T)) compose J^2 T e_(t t)) inter H$
  с условием $M'_(k m) = J T$. Ввиду выбора $M$ по лемме
  @lem:l2002-radical-normal-elimination определители матриц из множеств $e + M$
  и $e + M'$ равны 1 и поэтому $M' subset P_(k m) lr((J T)) inter H$. К
  множествам $[K e_(m,m-1), M]$ ($m > 1$) и $[K e_(k+1,k), M]$ ($k < n$)
  применимо индуктивное предположение. Получаем соответственно включения
  $H supset P_(k,m-1) lr((J T))$ и $H supset P_(k+1,m) lr((J T))$. Отсюда
  вытекают включения $H supset J T e_(k m)$ и $H supset P_(k m) lr((J T))$.
  Лемма доказана.
]

#lemma[
  Пусть $M subset H inter (P_(k m) lr((T)) + P_(1 m) lr((J T))
    + P_(k n) lr((J T)) + P_(1 n) lr((J^2 T)))$ и $M_(k m) = T$ для
  фиксированной позиции $(k, m)$, $k != m$, причем $det(alpha + e) = 1$ для всех
  $alpha in M$. Тогда $H supset P_(k m) lr((T))$.
] <lem:l2002-radical-normal-t-closure>

#proof[
  Множество $[J e_(1 k), M]$ лежит в $H$. При $k > 1$ к нему применима
  лемма~@lem:l2002-radical-normal-jt-closure, и с ее помощью получим
  $H supset P_(1 m) lr((J T))$. Аналогично при $m < n$ должны иметь
  $H supset P_(k n) lr((J T))$. Поскольку также по
  лемме~@lem:l2002-radical-normal-jjt $P_(1 n) lr((J^2 T)) subset H$, можно
  предполагать, что $M subset H inter P_(k m) lr((T))$ и по-прежнему
  $M_(k m) = T$. Включение $H supset P_(k m) lr((T))$ при $k > m$ вытекает
  сейчас из леммы~@lem:l2002-radical-normal-elementary-closure; при $k < m$ оно
  доказывается индукцией по $m - k$ по аналогии с доказательством предыдущей
  леммы. Лемма доказана.
]

Следующие леммы @lem:l2002-radical-normal-primary-basic–
@lem:l2002-radical-normal-generating-subgroups переносят на наш случай леммы
@lem:l2002-radical-lie-basic-subgroup и
@lem:l2002-radical-lie-generating-subgroups о включении в $H$ определенных
множеств.

#lemma[
  Если $(i, j) in Lc(H)$, то $H supset Q_(i+1,j-1) lr((T))$ при
  $2 <= j < i <= n - 1$ и $H supset P_(i+1,j-1) lr((T))$ при $i < j$.
] <lem:l2002-radical-normal-primary-basic>

#proof[
  Поскольку $H supset [e_(i+2,i+1), [e_(i+1,i), [K e_(j,j-1), H]]]$ и
  $H supset [e_(j-1,j-2), [e_(i+1,i), [K e_(j,j-1), H]]]$, из лемм
  @lem:l2002-radical-normal-elimination– @lem:l2002-radical-normal-t-closure
  вытекает первое включение, а также второе включение при $j = i + 2$. Случаи
  $j = i + 1$ и $i < j - 2$ рассматриваются аналогично с использованием
  соотношения $H supset [e_(i+1,i), [K e_(i+1,i), H]]$ и соответственно
  $H supset [e_(i+1,i), [H, K e_(j,j-1)]]$. Лемма доказана.
]

Аналогично лемме~@lem:l2002-radical-normal-primary-basic доказывается

#lemma[
  Если $(k, m) in Lc'(H)$, то $H supset Q_(k+1,m-1) lr((J T))$ при $k < m$ и
  $H supset P_(k+1,m-1) lr((J T))$ при $2 <= m < k <= n - 1$.
] <lem:l2002-radical-normal-secondary-basic>

#lemma[
  Пусть $(i, j) in Lc(H)$. Тогда $H$ содержит подгруппы $Q_(1,j-1) lr((J T))$,
  $Q_(i+1,n) lr((J T))$ при $1 < j < i < n$ и подгруппы $P_(1,j-1) lr((J T))$,
  $P_(i+1,n) lr((J T))$ при $i < j$.
] <lem:l2002-radical-normal-primary-border>

#proof[
  При $1 < j < i < n$ по лемме~@lem:l2002-radical-normal-jt-closure в силу
  включений $H supset [K e_(2 1), [e_(j,j-1), [J e_(1 i), H]]]$ и
  $H supset [e_(j-1,j-2), [e_(j,j-1), [J e_(1 i), H]]]$ имеем
  $H supset P_(2,j-1) lr((J T))$ и $H supset P_(1,j-2) lr((J T))$
  соответственно. Отсюда $H supset Q_(1,j-1) lr((J T))$. Включение
  $H supset Q_(i+1,n) lr((J T))$ получаем аналогично. Утверждение леммы для
  $i < j$ вытекает непосредственно из
  леммы~@lem:l2002-radical-normal-primary-basic. Лемма доказана.
]

Очевидно, если $Lc(H) = {(1, n)}$, то
$H compose D = Q_(1 n) lr((T)) compose (H_(1 n)e_(1 n)) compose D$
и по лемме~@lem:l2002-radical-normal-primary-basic
$H = Q_(1 n) lr((T)) compose (H inter (D compose H_(1 n)e_(1 n)))$.

#lemma[
  #source(16, printed: 434)Пусть $(i, j) in Lc(H)$. Тогда
  #letter-list(
    [$H supset P_(i,j-2) lr((T))$ при $j > 2$ и $H supset P_(i+2,j) lr((T))$ при
      $i < n - 1$;],
    [$H supset Q_(i j) lr((T))$ при $j = i + 1$;],
    [$H$ содержит подгруппы $Q_(i,j-1) lr((T))$, $Q_(i+1,j) lr((T))$ при
      $j = i + 2$;],
    [$H$ содержит подгруппы $P_(2 j) lr((J T))$, $P_(i,n-1) lr((J T))$;],
    [$H supset P_(1 j) lr((J T))$ при $i < n$ и $H supset P_(i n) lr((J T))$ при
      $j > 1$.],
  )
] <lem:l2002-radical-normal-primary-subgroups>

#proof[
  Утверждение (а) вытекает из лемм @lem:l2002-radical-normal-primary-basic,
  @lem:l2002-radical-normal-primary-border и соотношений
  $H supset [e_(j-1,j-2), [K e_(j,j-1), H]]$ и
  $H supset [e_(i+2,i+1), [K e_(i+1,i), H]]$. Применяя (а) к соотношению
  $H supset [K e_(i+1,i), H]$ и те же леммы, получаем утверждение (б). С помощью
  включений $H supset [e_(i+1,i), [K e_(i+2,i+1), H]]$ и
  $H supset [e_(i+2,i+1), [K e_(i+1,i), H]]$ аналогично доказывается утверждение
  (в).

  Утверждение (г) следует из включений $H supset [J e_(2 i), H]$,
  $H supset [J e_(j,n-1), H]$ и леммы~@lem:l2002-radical-normal-primary-border.
  По лемме~@lem:l2002-radical-normal-primary-subgroups (а) первое и второе
  включения в (д) выполняются при $i <= n - 2$ или $j >= 3$ соответственно или
  когда $i < j$. С другой стороны, используя включение
  $H supset [J e_(1 n), [e_(j,j-1), [K e_(n,n-1), H]]]$ при $i = n - 1$, находим
  $H supset P_(1,j-1) lr((J T))$. Случай $j = 2$ рассматривается аналогично.
  Лемма доказана.
]

Точно так же доказывается следующая

#lemma[
  Пусть $(k, m) in Lc'(H)$. Тогда
  #letter-list(
    [$H supset P_(k,m-2) lr((J T))$ при $m > 2$ и $H supset P_(k+2,m) lr((J T))$
      при $k < n - 1$;],
    [$H supset Q_(k m) lr((J T))$ при $m = k + 1$;],
    [$H$ содержит подгруппы $Q_(k,m-1) lr((J T))$, $Q_(k+1,m) lr((J T))$ при
      $m = k + 2$.],
  )
] <lem:l2002-radical-normal-secondary-subgroups>

#lemma[
  Множество ${x e_(1 1) + x' e_(n n) | x in J T}$ лежит в $H$.
] <lem:l2002-radical-normal-diagonal-subgroup>

#proof[
  Если существует матрица $lr(‖a_(s t)‖) in H$ такая, что
  $a_(1 1) compose a^*_(n n) ∉ J T$, то
  $J(a_(1 1) compose a^*_(n n)) + J^2 T = J T$ в силу сильной максимальности
  $J$. Поэтому, применяя лемму~@lem:l2002-radical-normal-jt-closure к множеству
  $[J e_(1 n), H]$ с $(1, n)$-проекцией $J T$, получим
  $H supset P_(1 n) lr((J T)) supset {x e_(1 1) + x' e_(n n) | x in J T}$.
  Допустим, что $a_(1 1) compose a^*_(n n) in J T$ для всякой матрицы
  $lr(‖a_(s t)‖) in H$. Тогда $[J e_(1 n), H] = [T e_(n 1), J e_(1 n)]$ по
  модулю $P_(1 n) lr((J^2 T))$ при $Lc = {(n, 1)}$. С другой стороны, нормальная
  подгруппа $H$ при $Lc != {(n, 1)}$ всегда содержит подмножество, у которого
  $(n, 1)$-проекция равна $T$, а остальные проекции лежат в $J T$. Поскольку
  $P_(1 n) lr((J^2 T)) compose P_(n 1) lr((J T)) subset H$ в силу лемм
  @lem:l2002-radical-normal-jjt и @lem:l2002-radical-normal-primary-subgroups
  (г), то во всех случаях получаем включение $H supset [T e_(n 1), J e_(1 n)]$.
  Принимая сейчас во внимание
  @eq:l2002-radical-elementary-commutator-factorization, получаем требуемое в
  лемме включение. Лемма доказана.
]

Напомним, что по лемме~@lem:l2002-radical-normal-corner-classification проекция
$T = H_(n 1)$ при $Lc(H) != {(n, 1)}$ — идеал кольца $K$. Исключительный случай
рассматривает

#lemma[
  #letter-list(
    [Если $Lc(H) = {(n, 1)}$, то $T$ есть $J$-подмодуль кольца $K$;],
    [если $lr(‖a_(s t)‖) in H$, то $J(a^*_(k k) compose a_(m m)) subset H_(k m)$
      для всех $k != m$ и $K(a^*_(k k) compose a_(m m)) subset H_(k m)$ при
      $k > m$.],
  )
] <lem:l2002-radical-normal-exceptional-projection>

#proof[
  (а) Пусть $alpha = lr(‖a_(s t)‖)$, $beta = lr(‖b_(s t)‖) in H$. Из условия
  леммы следует, что $H^2 subset P_(1 n) lr((J T))$, и по лемме
  @lem:l2002-radical-normal-primary-subgroups (г) $H supset J T e_(n 1)$. В
  частности, $J T subset T$. Поскольку
  $alpha compose beta = alpha + beta + alpha beta$, то $(n, 1)$-проекции в
  $alpha compose beta$ и $alpha + beta$ различаются на элемент $c_1 in J T$, в
  $alpha compose beta compose (-c_1 e_(n 1))$ и $alpha + beta$ — на элемент
  $c_2 in J^2 T$, в
  $alpha compose beta compose (-c_1 e_(n 1)) compose (-c_2 e_(n 1))$
  и $alpha + beta$ — на элемент $c_3 in J^3 T$, и т. д. В силу нильпотентности
  идеала $J$ через конечное число шагов найдется элемент $gamma in J T e_(n 1)$
  такой, что $(n, 1)$-проекция произведения $alpha compose beta compose gamma$
  равна $a_(n 1) + b_(n 1)$. Аналогично существует элемент
  $gamma in J T e_(n 1)$ такой, что $(n, 1)$-проекция произведения
  $alpha' compose gamma$ равна $-a_(n 1)$. Это доказывает аддитивность $T$.

  #source(17, printed: 435)Обозначим через $H_0$ подгруппу присоединенной
  группы, порожденную множествами из $H$, перечисленными в леммах
  @lem:l2002-radical-normal-jjt, @lem:l2002-radical-normal-primary-basic –
  @lem:l2002-radical-normal-diagonal-subgroup. Тогда утверждение (б) следует из
  соотношений @eq:l2002-radical-offdiagonal-commutator и включения
  $H supset H_0$. Лемма доказана.
]
