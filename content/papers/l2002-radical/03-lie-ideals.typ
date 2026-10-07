#import "defs.typ": *

=== Теорема об идеалах ассоциированного кольца Ли
<sec:l2002-radical-lie-ideals>

Цель параграфа — доказать следующую теорему.

#theorem[
  Пусть $J$ — сильно максимальный идеал кольца $K$ со свойством $2 I = I$ для
  любого идеала $I subset.eq J$ кольца $K$. Если $H$ — идеал лиева кольца
  $R_n lr((K, J))$, $n >= 2$, и $T$ — его $(n, 1)$-проекция, то существует и
  единственна лиева $T$-граница $A = A_L lr((T; Lc, Lc'))$ кольца
  $R_n lr((K, J))$, порождающая $H$ как лиев идеал, причем
  $A = H inter (tilde(B) + D)$.
] <th:l2002-radical-lie-boundary>

По существу, при ограничениях $n > 4$ и $2 K = K$
теорему~@th:l2002-radical-lie-boundary без утверждения единственности
устанавливает основная теорема в [@bib:l2002-radical-Suleimanova2000b]; схема ее
доказательства существенно используется ниже.

Ассоциированное лиево умножение в кольце $R = R_n lr((K, J))$ обозначаем через
$ast$, т.~е. $alpha ast beta = alpha beta - beta alpha$. Через $Lambda(R)$
обозначаем ассоциированное лиево кольцо. Основные соотношения между матричными
единицами дают следующую формулу:
$
  alpha ast (x e_(k m)) = x(sum_(s=1)^n a_(s k)e_(s m)
    - sum_(t=1)^n a_(m t)e_(k t))
  quad (alpha = lr(‖a_(s t)‖), x in K).
$ <eq:l2002-radical-elementary-lie-product>

#lemma[
  Пусть $H$ — идеал лиева кольца $Lambda(R)$. Тогда

  (а) $J H_(u v) subset H_(i j)$ при $u != v$;

  (б) если $(i, j) ≻ (u, v)$ и $u != v$, то $2 K H_(u,u+1) subset H_(u+1,u)$,
  когда $v = u + 1$ и $(i, j) = (u + 1, u)$, и $K H_(u v) subset H_(i j)$ в
  остальных случаях;

  (в) если $lr(‖a_(k m)‖) in H$ и $u > v$, то
  $K(a_(v v) - a_(u u)) subset H_(u v)$ и $J(a_(v v) - a_(u u)) subset H_(v u)$;

  (г) если $T = H_(n 1)$, то $T$ — $J$-подмодуль кольца $K$ и либо
  $K H_(u v) != T$ для всех $(u, v) != (n, 1)$, $u != v$, либо $T$ — идеал
  кольца $K$.
] <lem:l2002-radical-lie-projections>

#proof[
  Следует из @eq:l2002-radical-elementary-lie-product; см. также лемму 1 из
  [@bib:l2002-radical-Suleimanova2000b].
]

Пусть $Lc(H)$ — множество всех минимальных относительно введенного упорядочения
$≽$ матричных позиций $(i, j)$, не лежащих на главной диагонали и таких, что
идеал, порожденный $H_(i j)$, содержит $T$. Через $Lc'(H)$ обозначаем множество
(возможно, пустое) всех минимальных относительно упорядочения $≽$ #source(
  6,
  printed: 424,
)матричных позиций $(k, m)$, $k != m$, для которых $H_(k m)$ порождает идеал
$J T$, причем $k < i$ и $m > j$ для всех $(i, j) in Lc(H)$.

#lemma[
  Пусть $H$ — лиев идеал кольца $R_n lr((K, J))$, $Lc = Lc(H)$ и $Lc' = Lc'(H)$.
  Тогда $Lc$, $Lc'$ — множество углов степени $n$. Если $J$ — сильно
  максимальный идеал кольца $K$, то при $(k, m) in.not Lc union Lc'$, $k != m$,
  имеем либо $(k, m) ≻ Lc$ и $H_(k m) = T$, либо $(k, m) ≻ Lc'$, $(k, m) ⊁ Lc$ и
  $H_(k m) = J T$, либо $(k, m) ⊁ Lc'$ и $H_(k m) = J^2 T$.
] <lem:l2002-radical-lie-corner-classification>

#proof[
  С учетом леммы~@lem:l2002-radical-lie-projections первое утверждение вытекает
  из определений множества углов и множеств $Lc$, $Lc'$. Пусть $J$ — сильно
  максимальный идеал кольца $K$. По лемме~@lem:l2002-radical-lie-projections
  всякая недиагональная проекция $H_(k m)$ лежит в $T$ и содержит $J^2 T$.
  Следовательно, если она содержит $J T$, то совпадает с $T$ или $J T$; при
  $H_(k m) subset J T$ проекция $H_(k m)$ должна совпадать с $J T$ или $J^2 T$ в
  силу выбора $J$. Учитывая определения $Lc$, $Lc'$ и то, что при $(i, j) in Lc$
  лемма~@lem:l2002-radical-lie-projections дает также включения
  $H_(1 j) supset J H_(i j) = J K H_(i j) = J T$ и
  $H_(i n) supset J H_(i j) = J K H_(i j) = J T$, получаем второе утверждение
  леммы (см. матрицу (@fig:l2002-radical-corner-matrix)). Лемма доказана.
]

Далее предполагаем, что $J$ — сильно максимальный идеал кольца $K$, $H$ —
фиксированный лиев идеал кольца $R_n lr((K, J))$, $Lc = Lc(H)$ и $Lc' = Lc'(H)$.
По лемме~@lem:l2002-radical-lie-projections $T = H_(n 1)$ является
$J$-подмодулем, а при $Lc != {(n, 1)}$ — даже идеалом кольца $K$. Наша цель —
показать, что $H$ порождается как лиев идеал подходящей лиевой $T$-границей
$A_L lr((T; Lc, Lc'))$.

В этом параграфе через $P_(i j) lr((F))$ (аналогично $Q_(i j) lr((F))$) при
$F subset.eq K$ обозначаем аддитивную подгруппу кольца $R$, порожденную
множествами $F e_(k m)$ для всех $(k, m) ≽ (i, j)$ (соответственно
$(k, m) ≻ (i, j)$), $k != m$, и при $i < j$ еще множествами
$F(e_(k k) - e_(m m))$, $i <= k < m <= j$.

#lemma[
  Пусть $H$ — лиев идеал кольца $R_n lr((K, J))$ и $H_0$ — аддитивная подгруппа
  $
    sum_((i,j) in Lc,i<j) [Q_(i+1,j) lr((T)) + Q_(i,j-1) lr((T))]
    + sum_((i,j) in Lc,i>j) [P_(i+2,j) lr((T)) + P_(i,j-2) lr((T))]
    + sum_((i,i+1) in Lc) Q_(i,i+1) lr((T)) + (J T)(e_11 - e_(n n))
    + sum_((i,j) in Lc) [Q_(1,j-1) lr((J T)) + P_(2 j) lr((J T))]
    + sum_((i,j) in Lc) [Q_(i+1,n) lr((J T)) + P_(i,n-1) lr((J T))]
    + sum_((k,m) in Lc',k>m) [Q_(k+1,m) lr((J T)) + Q_(k,m-1) lr((J T))]
    + sum_((k,m) in Lc',k<m) [P_(k+2,m) lr((J T)) + P_(k,m-2) lr((J T))]
    + sum_((k,k+1) in Lc') Q_(k,k+1) lr((J T)) + P_(1 n) lr((J^2 T)).
  $ <eq:l2002-radical-lie-basic-subgroup>
  Если любой идеал $I subset.eq J$ кольца $K$ удовлетворяет условию $2 I = I$,
  то $H supset.eq H_0$.
] <lem:l2002-radical-lie-basic-subgroup>

#proof[
  Поскольку идеал $J^2 T$ кольца $K$ лежит в $J$, то $2 J^2 T = J^2 T$ в силу
  выбора $J$ в лемме. Поэтому $H$ содержит множество
  $
    J^2 H_(n 1)e_(1 n) = J^2(2 H_(n 1))e_(1 n)
    = (J e_(1 n) ast H) ast J e_(1 n)
  $
  и его лиево замыкание $P_(1 n) lr((J^2 T))$. Следовательно, включение
  $H supset P_(1 n) lr((J^2 T))$, доказанное в лемме 2 из
  [@bib:l2002-radical-Suleimanova2000b] при условии $2 K = K$, выполняется и при
  нашем более слабом ограничении на $J$, $K$. Включение в $H$ остальных
  порождающих из @eq:l2002-radical-lie-basic-subgroup получаем аналогично, как и
  в леммах 2–8 из [@bib:l2002-radical-Suleimanova2000b], опираясь на уже
  доказанное включение. Лемма доказана.
]

#source(7, printed: 425)Сопоставим с каждой матрицей $lr(‖a_(s t)‖)$ кольца
$R_n lr((K, J))$ следующие аддитивные подгруппы:
$
  P_(i j) lr((T)) + P_(1 j) lr((J T)) + P_(i n) lr((J T))
  quad "при" i > j, quad a_(i i) != a_(j j) mod J T;
$ <eq:l2002-radical-lie-diagonal-jt>
$
  P_(i j) lr((J T)), quad "если" J(a_(i i) - a_(j j)) != 0 mod J^2 T
  quad "или" i > j, quad a_(i i) != a_(j j) mod J^2 T;
$ <eq:l2002-radical-lie-diagonal-jjt>
$
  K(a_(i j)e_(i,j-1) - a_(j-1,i+1)e_(j,i+1)
    + a_(i+1,j)e_(i+1,j-1) - a_(j-1,i)e_(j i)),
  quad K(a_(i j)e_(i+1,j) - a_(j-1,i+1)e_(j-1,i)
    + a_(i,j-1)e_(i+1,j-1) - a_(j,i+1)e_(j i)),
  quad K(a_(i j)e_(i+1,j-1) + a_(j-1,i+1)e_(j i))
  quad ((i, j) in Lc, (j - 1, i + 1) in Lc');
$ <eq:l2002-radical-lie-coupled-corners>
$
  K(a_(i j)e_(i,j-1) - a_(j-1,m)e_(j m))
  quad ((i, j), (j - 1, m) in Lc union Lc',
    m != i + 1, (i, m) != (n, 1));
$ <eq:l2002-radical-lie-adjacent-corners>
$
  K(a_(n j)e_(n,j-1) - a_(j-1,1)e_(j 1)
    + a_(1 j)e_(1,j-1) - a_(j-1,n)e_(j n)),
  quad J(a_(n j)e_(1 j) - a_(j-1,1)e_(j-1,n)
    + a_(n,j-1)e_(1,j-1) - a_(j 1)e_(j n)),
  quad J(a_(n j)e_(1,j-1) + a_(j-1,1)e_(j n))
  quad ((n, j), (j - 1, 1) in Lc);
$ <eq:l2002-radical-lie-border-coupled-corners>
$
  J(a_(n j)e_(1 j) - a_(i 1)e_(i n))
  quad ((n, j), (i, 1) in Lc, i != j - 1).
$ <eq:l2002-radical-lie-border-separated-corners>

#lemma[
  Лиев идеал $H$ содержит следующие аддитивные подгруппы:

  (а) $P_(k m) lr((T))$, если либо $(k - 1, m)$ — угол из $Lc$, не являющийся
  лево-связанным, либо $(k, m + 1)$ — угол из $Lc$, не являющийся
  право-связанным, либо $(k - 1, m + 1) in Lc$ и $(m, k) in.not Lc'$;

  (б) $P_(k m) lr((J T))$, если либо $(k - 1, m)$ — угол из $Lc'$, не являющийся
  лево-связанным, либо $(k, m + 1)$ — угол из $Lc'$, не являющийся
  право-связанным, либо $(k - 1, m + 1) in Lc'$ и $(m, k) in.not Lc$;

  (в) $P_(1 j) lr((J T))$, если либо $(n, j + 1) in Lc$ лево-связанный с углом
  из $Lc$, но не является право-связанным с этим углом, либо $(n, j) in Lc$ —
  угол, не являющийся лево-связанным, либо $(i, j) in Lc$ для $i < n$;

  (г) $P_(i n) lr((J T))$, если либо $(i - 1, 1) in Lc$ право-связан с углом из
  $Lc$, но не является лево-связанным с этим углом, либо $(i, 1) in Lc$ — угол,
  не являющийся право-связанным, либо $(i, j) in Lc$ для $j > 1$.

  Кроме того, $H$ содержит множества @eq:l2002-radical-lie-diagonal-jt–
  @eq:l2002-radical-lie-border-separated-corners для любой матрицы
  $lr(‖a_(s t)‖) in H$.
] <lem:l2002-radical-lie-generating-subgroups>

#proof[
  Отметим, что включение в $H$ аддитивных подгрупп (а) и (б) при $k = m$, а
  также (в) при $j = 1$ и (г) при $i = n$ вытекает из
  леммы~@lem:l2002-radical-lie-basic-subgroup.

  Покажем, что множество @eq:l2002-radical-lie-diagonal-jt лежит в $H$. При
  $i - j > 1$, пользуясь включением $H supset H ast K e_(i j) + H_0$, находим
  $H supset K{a_(i i) - a_(j j) | lr(‖a_(s t)‖) in H}e_(i j)$. Кроме того, в
  условиях @eq:l2002-radical-lie-diagonal-jt $(i, j) ≽ Lc$, и поэтому
  $H supset J T e_(i j)$ в силу леммы~@lem:l2002-radical-lie-basic-subgroup.
  Идеал $K{a_(i i) - a_(j j) | lr(‖a_(s t)‖) in H} + J T$ кольца $K$ лежит между
  $J$-подмодулями $J T$ и $T$, не совпадает с $J T$ и, значит, совпадает с $T$,
  поскольку $J$ — сильно максимальный идеал. Таким образом, получаем включение в
  $H$ множества $T e_(i j)$, а следовательно, и множества
  $P_(i j) lr((T)) + P_(1 j) lr((J T)) + P_(i n) lr((J T))$, так как $H$ — лиев
  идеал. То же самое включение получим и при $j = i - 1$. Нужно лишь заметить,
  что множество $H ast K e_(i j) + J T e_(i j)$ лежит в пересечении
  $
    (T e_(i j) + T e_(i,j-1) + T e_(i+1,i) + H_0) inter H
  $
  и имеет $(i, j)$-проекцию, равную $T$. Включение $P_(i j) lr((J T)) subset H$
  в условиях @eq:l2002-radical-lie-diagonal-jjt доказывается аналогично.

  Рассмотрим (а). В первом случае, когда $(k - 1, m) in Lc$, множество
  $H ast K e_(k,k-1)$ по модулю $H_0$ лежит в
  $(T e_(k m) + T e_(k,k-1) + J T e_(k n)) inter H$, причем его
  $(k, m)$-проекция равна $T$. Если $H supset P_(k,k-1) lr((T))$, то для $m > k$
  требуемое включение $H supset P_(k m) lr((T))$ получим из равенства
  $H ast K e_(k,k-1) = T e_(k m) mod Q_(k m) lr((T))$. #source(
    8,
    printed: 426,
  )При $H ⊅ P_(k,k-1) lr((T))$ имеем $m < k$ и, значит, последнее равенство
  также выполняется. Второй случай рассматривается аналогично с помощью
  соотношения $H supset H ast K e_(m+1,m) mod H_0$. В третьем случае
  $H supset (H ast K e_(m+1,m)) ast e_(k,k-1) = T e_(k m) mod H_0$. Включения в
  случае (б) доказываются аналогично.

  Если в случае (в) $(i, j) in Lc$, то при $i <= n - 2$ по
  лемме~@lem:l2002-radical-lie-basic-subgroup $H supset P_(i+2,j) lr((T))$ и
  $H supset P_(1 j) lr((J T))$. При $i = n - 1$ имеем
  $
    (H ast K e_(n,n-1)) ast J e_(1 n)
    subset (J T e_(1 j) + J T e_(1,n-1) + H_0) inter H
  $
  и поэтому либо $H supset P_(1,n-1) lr((J T))
  supset P_(1 j) lr((J T))$, либо $H ⊅ P_(1,n-1) lr((J T))$, так что
  $j != n - 1$ и $(H ast K e_(n,n-1)) ast J e_(1 n)
  = J T e_(1 j) mod Q_(1 j) lr((J T))$, откуда вновь
  $H supset P_(1 j) lr((J T))$. Это же включение при $(n, j + 1) in Lc$,
  $(j, 1) in.not Lc$ получаем аналогично с помощью соотношения
  $H supset (H ast K e_(j+1,j)) ast J e_(1 n)$. Если угол $(n, j)$ лежит в $Lc$
  и не является лево-связанным, то $H supset T e_(n,j-1) + J T e_(1,j-1)$ по
  доказанному и с учетом включения в $H$ множеств $H ast J e_(1 n)$, $H_0$ и
  @eq:l2002-radical-lie-diagonal-jjt вновь находим $H supset J T e_(1 j)$.

  Включение $H supset P_(i n) lr((J T))$ в случае (г) доказывается аналогично.

  Ясно, что $H$ содержит лиевы произведения
  $
    e_(i+1,i) ast (H ast K e_(j,j-1)),
    quad J e_(1 n) ast (H ast K e_(j,j-1))
  $
  и, как следствие, последние множества из @eq:l2002-radical-lie-coupled-corners
  и @eq:l2002-radical-lie-border-coupled-corners соответственно. Прибавляя к
  произведению $J e_(1 n) ast alpha$ матрицы из $H_0$ и из множеств (а)–(г) и
  @eq:l2002-radical-lie-diagonal-jjt, получаем включение в $H$ множества
  @eq:l2002-radical-lie-border-separated-corners при $i != j - 1$ и второго
  множества из @eq:l2002-radical-lie-border-coupled-corners для $i = j - 1$.
  Аналогично, используя включения в $H$ множеств (а)–(г),
  @eq:l2002-radical-lie-diagonal-jt, лиевых произведений $K e_(i+1,i) ast H$,
  $H ast K e_(j,j-1)$, а также лемму~@lem:l2002-radical-lie-basic-subgroup,
  выводим включения в $H$ первого множества из
  @eq:l2002-radical-lie-border-coupled-corners и множеств
  @eq:l2002-radical-lie-coupled-corners, @eq:l2002-radical-lie-adjacent-corners.
  Лемма доказана.
]

#lemma[
  Пусть $alpha$ — произвольная матрица из лиева идеала $H$, а $tilde(B)$ и $D$
  определены по формуле @eq:l2002-radical-enlarged-support. Тогда в пересечении
  $H inter (tilde(B) + D)$ существует матрица с такими же, как и у $alpha$,
  $(u, v)$-проекциями при $u = v$ и для всех $(u, v) in Lc union Lc'$. Кроме
  того, $H$ аддитивно порождается пересечением $H inter (tilde(B) + D)$ и
  множествами @eq:l2002-radical-lie-basic-subgroup, (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups, а также множествами
  @eq:l2002-radical-lie-diagonal-jt–
  @eq:l2002-radical-lie-border-separated-corners для всевозможных
  $lr(‖a_(s t)‖) in H$.
] <lem:l2002-radical-lie-reduction>

#proof[
  Пусть $alpha = lr(‖a_(s t)‖) in H$. Все недиагональные проекции $H_(k m)$ и,
  следовательно, $a_(k m)$ ($k != m$), лежат в $T$, $J T$ или в $J^2 T$ в
  соответствии с их описанием в
  лемме~@lem:l2002-radical-lie-corner-classification. В частности, если
  $(k, m) ⋡ Lc'$, то $a_(k m) in J^2 T$. По
  лемме~@lem:l2002-radical-lie-basic-subgroup имеем
  $P_(1 n) lr((J^2 T)) subset H$. Поэтому, прибавляя к $alpha$ элементарные
  матрицы $-a_(k m)e_(k m)$ для всевозможных указанных $(k, m)$, находим в $H$
  матрицу, у которой все недиагональные $(u, v)$-проекции при $(u, v) ⋡ Lc'$
  равны нулю, а остальные проекции такие же, как у $alpha$. Далее, аналогично
  прибавляем к $alpha$ элементарные матрицы из $H$, которые выбираются из
  множества @eq:l2002-radical-lie-basic-subgroup и из множеств (а)–(г)
  леммы~@lem:l2002-radical-lie-generating-subgroups. Получим матрицу, у которой
  все элементы на недиагональных позициях вне $tilde(Lc) union tilde(Lc)'$
  являются нулевыми, исключая при $n > 2$, быть может, следующие позиции:

  (а) $(j - 1, i)$, $(j, i + 1)$ или $(j, i)$, когда $(i, j) in Lc$ и
  $(j - 1, i + 1) in Lc'$;

  (б) $(i, j - 1)$ или $(i + 1, j)$, когда $(i, j)$ — право- или соответственно
  лево-связанный угол, причем $(j - 1, i + 1) in.not Lc union Lc'$;

  (в) $(1, j)$, если $(n, j)$ — лево-связанный угол, и еще позиция $(1, j - 1)$,
  когда $(n, j)$ и $(j - 1, 1)$ лежат в $Lc$.

  По лемме~@lem:l2002-radical-lie-generating-subgroups в исключительном случае
  (а) можно обратить в нуль $(j - 1, i)$- и $(j, i + 1)$-проекции матрицы
  $alpha$, прибавляя к ней матрицы из первых двух множеств в
  @eq:l2002-radical-lie-coupled-corners. Используя также прибавления матриц из
  последнего множества в @eq:l2002-radical-lie-coupled-corners, обращаем в нуль
  $(j, i)$-проекцию $alpha$. Исключительные случаи (б), (в) #source(
    9,
    printed: 427,
  )рассматриваем аналогично, учитывая множества
  @eq:l2002-radical-lie-adjacent-corners–
  @eq:l2002-radical-lie-border-separated-corners и
  лемму~@lem:l2002-radical-lie-generating-subgroups. Лемма доказана.
]

Основной в доказательстве теоремы~@th:l2002-radical-lie-boundary является
следующая

#lemma[
  Пусть $H$ — идеал лиева кольца $R_n lr((K, J))$, а $tilde(B)$ и $D$ определены
  по формуле @eq:l2002-radical-enlarged-support. Тогда пересечение
  $H inter (tilde(B) + D)$ порождает $H$ как лиев идеал и является лиевой
  $T$-границей в $R_n lr((K, J))$.
] <lem:l2002-radical-lie-boundary-existence>

#proof[
  Положим $A = H inter (tilde(B) + D)$. По
  лемме~@lem:l2002-radical-lie-reduction $(k, m)$-проекции множеств $A$ и $H$
  совпадают при $(k, m) in Lc union Lc'$ и, следовательно, условия
  @cond:l2002-radical-boundary-degeneracy и
  @cond:l2002-radical-boundary-projections для $A$ выполняются. Используя
  включение $J tilde(B) subset H_0$, получаем
  $J tilde(B) subset A subset tilde(B) + D$, так что $A$ удовлетворяет условию
  @cond:l2002-radical-lie-support. Свойства @cond:l2002-radical-lie-diagonal-jt
  и @cond:l2002-radical-lie-diagonal-jjt для $A$ также выполняются в силу
  утверждения леммы~@lem:l2002-radical-lie-reduction о диагоналях матриц из
  пересечения $H inter (tilde(B) + D)$.

  По лемме~@lem:l2002-radical-lie-reduction множества
  @eq:l2002-radical-lie-basic-subgroup, (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups и множества
  @eq:l2002-radical-lie-diagonal-jt–
  @eq:l2002-radical-lie-border-separated-corners для всевозможных
  $lr(‖a_(s t)‖) in H$, вместе с $A$, аддитивно порождают $H$, см. матрицу
  (@fig:l2002-radical-corner-matrix). Кроме того, по
  лемме~@lem:l2002-radical-lie-reduction множества
  @eq:l2002-radical-lie-basic-subgroup, (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups, а также
  @eq:l2002-radical-lie-diagonal-jt, @eq:l2002-radical-lie-diagonal-jjt,
  @eq:l2002-radical-lie-adjacent-corners и
  @eq:l2002-radical-lie-border-separated-corners для всевозможных
  $lr(‖a_(s t)‖) in H$ полностью определяются множеством углов $Lc$, $Lc'$ и
  диагоналями матриц из $A$, так что в силу лемм
  @lem:l2002-radical-lie-basic-subgroup и
  @lem:l2002-radical-lie-generating-subgroups все они лежат в лиевом замыкании
  множества $A$. Очевидно, то же самое верно и для последнего множества как в
  @eq:l2002-radical-lie-coupled-corners, так и в
  @eq:l2002-radical-lie-border-coupled-corners. Порождаемость $H$ как лиева
  идеала множеством $A$ сейчас будет доказана, если мы покажем, что оставшиеся
  множества в @eq:l2002-radical-lie-coupled-corners и
  @eq:l2002-radical-lie-border-coupled-corners также лежат в лиевом замыкании
  множества $A$. Для любой матрицы $alpha = lr(‖a_(s t)‖) in R_n lr((K, J))$
  положим
  $
    phi_(i j) lr((alpha)) = a_(i j)e_(i+1,j-1)
    + a_(j-1,i+1)e_(j i),
  $
  $
    phi^+_(i j) lr((alpha)) = a_(i j)e_(i,j-1)
    - a_(j-1,i+1)e_(j,i+1) + a_(i+1,j)e_(i+1,j-1)
    - a_(j-1,i)e_(j i),
  $
  $
    phi^-_(i j) lr((alpha)) = a_(i j)e_(i+1,j)
    - a_(j-1,i+1)e_(j-1,i) + a_(i,j-1)e_(i+1,j-1)
    - a_(j,i+1)e_(j i).
  $
  По лемме~@lem:l2002-radical-lie-generating-subgroups множества
  $K phi_(i j) lr((H))$, $K phi^+_(i j) lr((H))$ и $K phi^-_(i j) lr((H))$ лежат
  в $H$ при любом выборе $(i, j) in Lc$, $(j - 1, i + 1) in Lc'$. Первое из них,
  как уже отмечалось, лежит даже в лиевом замыкании множества $A$; докажем это
  же включение для оставшихся множеств.

  Пусть $alpha = lr(‖a_(s t)‖) in H$. В силу выбора $(i, j)$ и лемм
  @lem:l2002-radical-lie-projections,
  @lem:l2002-radical-lie-corner-classification $(j, i)$-, $(j - 1, i)$- и
  $(j, i + 1)$-проекции $H$ совпадают с идеалом $J T$, который, в свою очередь,
  порождается $(j - 1, i + 1)$-проекцией $H$. Поэтому существует конечное
  семейство матриц $gamma^((k)) = lr(‖c_(u v)^((k))‖) in H$ таких, что
  $
    a_(j-1,i) = sum_k x_k c_(j-1,i+1)^((k)),
    quad a_(j,i+1) = sum_k y_k c_(j-1,i+1)^((k)),
  $
  $
    a_(j i) - sum_k x_k c_(j,i+1)^((k))
    - sum_k y_k c_(j-1,i)^((k)) = -sum_k z_k c_(j-1,i+1)^((k))
  $
  для некоторых элементов $x_k$, $y_k$, $z_k in K$. Поскольку матрица
  $
    alpha + sum_k x_k phi^-_(i j) lr((gamma^((k))))
    + sum_k y_k phi^+_(i j) lr((gamma^((k))))
    + sum_k z_k phi_(i j) lr((gamma^((k)))) = overline(alpha)
  $
  имеет нулевые $(j, i)$-, $(j - 1, i)$- и $(j, i + 1)$-проекции, то матрицы
  $phi^+_(i j) lr((overline(alpha)))$ и $phi^-_(i j) lr((overline(alpha)))$
  лежат в лиевом замыкании множества $A$. Кроме того,
  $
    phi^+_(i j) lr((alpha)) = phi^+_(i j) lr((overline(alpha)))
    - sum_k x_k phi_(i j) lr((gamma^((k)))),
    quad phi^-_(i j) lr((alpha)) = phi^-_(i j) lr((overline(alpha)))
    - sum_k y_k phi_(i j) lr((gamma^((k)))).
  $
  #source(10, printed: 428)Отсюда уже следует, что $phi^+_(i j) lr((alpha))$ и
  $phi^-_(i j) lr((alpha))$ лежат в лиевом замыкании множества $A$.

  При $1 < j < n$ полагаем
  $
    phi_j lr((alpha)) = a_(n j)e_(1,j-1) + a_(j-1,1)e_(j n),
  $
  $
    phi^+_j lr((alpha)) = a_(n j)e_(n,j-1) - a_(j-1,1)e_(j 1)
    + a_(1 j)e_(1,j-1) - a_(j-1,n)e_(j n),
  $
  $
    phi^-_j lr((alpha)) = a_(n j)e_(1 j) - a_(j-1,1)e_(j-1,n)
    + a_(n,j-1)e_(1,j-1) - a_(j 1)e_(j n).
  $
  При $(n, j)$, $(j - 1, 1) in Lc$ множества $J phi_j lr((H))$,
  $J phi^-_j lr((H))$ и $K phi^+_j lr((H))$ из
  @eq:l2002-radical-lie-border-coupled-corners лежат в $H$ по
  лемме~@lem:l2002-radical-lie-generating-subgroups. Более того, как и выше,
  показывается, что они лежат даже в лиевом замыкании множества $A$.

  Таким образом, $H$ порождается как лиев идеал множеством $A$. Очевидно также,
  что если $A subset A_1 subset tilde(B) + D$ и $A_1$ порождает $H$ как лиев
  идеал, то $A_1 subset H inter (tilde(B) + D) = A$ и $A_1 = A$. Поэтому условие
  @cond:l2002-radical-lie-maximality для $A$ также выполняется и $A$ является
  лиевой $T$-границей. Лемма доказана.
]

Сейчас теорема~@th:l2002-radical-lie-boundary легко следует из лемм
@lem:l2002-radical-lie-corner-classification и
@lem:l2002-radical-lie-boundary-existence. Попутно доказана

#lemma[
  Пусть $A = A_L lr((T; Lc, Lc'))$ — произвольная лиева $T$-граница кольца
  $R_n lr((K, J))$. Тогда минимальный лиев идеал в $R_n lr((K, J))$, содержащий
  $A$, аддитивно порождается множествами $A$,
  @eq:l2002-radical-lie-basic-subgroup, (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups и еще множествами
  @eq:l2002-radical-lie-diagonal-jt–
  @eq:l2002-radical-lie-border-separated-corners для всевозможных матриц
  $lr(‖a_(s t)‖) in A$.
] <lem:l2002-radical-lie-boundary-generators>
