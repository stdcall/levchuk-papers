#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": NT, proposition

=== <sec:l1987-rings-automorphism-theorem>

Основным результатом является

#theorem[Пусть $K$ — кольцо с единицей без делителей нуля, $|Gamma| > 4$. Тогда
  всякий автоморфизм кольца $R = NT(Gamma, K)$ является произведением сдвига,
  диагонального, кольцевого, центрального и локально внутреннего автоморфизмов.
  Всякий автоморфизм группы $cal(G)(R)$ (аналогично, кольца $Lambda(R)$)
  является произведением #source(8, printed: 637) автоморфизма кольца $R$,
  гиперцентрального автоморфизма и еще, может быть,
  антисдвига.] <th:l1987-rings-automorphisms>

#proof[Пусть $tilde(Gamma)$ — совокупность отрезков цепи $Gamma$, отличных от
  $emptyset$, $Gamma$, $N_(i j) = 〈K epsilon_(u v) | u > v, u >= i, v <= j〉$,
  $phi in Aut cal(G)(R) union Aut Lambda(R)$.

  #enum(
    numbering: ru-enum,
    [Исследуем абелев идеал $B = N_(S T)^phi$ ($overline(S), T in tilde(Gamma)$,
      $S inter T = emptyset$), который не записывается в виде $N_(C D)$. Пусть
      вначале $overline(S) inter overline(T) != emptyset$. Очевидно, $B$
      является и пересечением, и взаимным коммутантом максимальных абелевых
      идеалов $N_(overline(T) T)^phi$ и $N_(S overline(S))^phi$; при
      $phi in Aut cal(G)(R)$ учитываем также теорему @th:l1987-rings-normal-lie,
      2). По теореме @th:l1987-rings-maximal-abelian получаем $p, q in Gamma$,
      ${N_(overline(T) T)^phi, N_(S overline(S))^phi}
      = {M_(i j)(frak(N)), N_(i j)}$
      при подходящем $frak(N)$ с ненулевыми $frak(N)_(11)$, $frak(N)_(22)$,
      $i, j in Gamma$, $p < i ◁ j < q$. Централизатор $C(B)$ лежит в
      $K epsilon_(i p) + K epsilon_(q j) + N_(i j)$, и так как
      $C(N_(S T)) = N_(overline(T) overline(S))$, то
      $N_(overline(T) overline(S))^3 subset K epsilon_(q p)$. Для $|Gamma| > 4$
      это возможно лишь при $|overline(S) inter overline(T)| <= 1$, так что
      $overline(S) inter overline(T) = {l}$. Поэтому существуют $k, m in Gamma$,
      $m ◁ l ◁ k$; в противном случае идеал
      $N_(S T) = 〈K epsilon_(u v) | v < l < u〉$ порождается идеалами вида
      $N_(C D)$, $|overline(C) inter overline(D)| > 1$, и, по доказанному,
      $N_(S T)^phi$ имеет вид $N_(C D)$. Следовательно, идеалы
      $N_(S overline(S))$ ($= N_(k l)$), $N_(overline(T) T)$, а потому и
      $M_(i j)(frak(N))$ не лежат в коммутанте $R^2$, откуда $p ◁ i$ или
      $j ◁ q$. При $overline(S) inter overline(T) = emptyset$ имеем
      $S = overline(T)$, и, по доказанному, идеал $N_(overline(T) T)$ не
      порождается идеалами вида $N_(C D)$ ($overline(C), D in tilde(Gamma)$,
      $overline(C) inter overline(D) != emptyset$). Следовательно,
      $N_(overline(T) T) = N_(i j)$ для некоторых $i, j in Gamma$, $j ◁ i$, и
      $N_(i j)^phi subset.not R^2$. Итак, для всех $T in tilde(Gamma)$ идеал
      $N_(overline(T) T)^phi$ либо совпадает с $N_(overline(T') T')$
      ($T' in tilde(Gamma)$), либо является максимальным абелевым идеалом, не
      лежащим в коммутанте $R^2$. По модулю коммутанта $phi$ индуцирует
      автоморфизм. Поэтому, в силу теоремы @th:l1987-rings-maximal-abelian,
      существует подстановка $'$ множества $tilde(Gamma)$, для которой
      $N_(overline(T) T)^phi = N_(overline(T') T')$ по модулю $Z'_3$
      ($T in tilde(Gamma)$), где $Z'_3$ при $p, q in Gamma$ есть пересечение
      идеалов $N_(i p)+N_(q j)$ ($i ≪ q$, $p ≪ j$), а в остальных случаях
      $Z'_3 = 0$.],

    [Отношение $subset$ для отрезков $Gamma$ дает линейное упорядочение
      множества $tilde(Gamma)$. Положим $N_T = N_(overline(T) T)$
      ($T in tilde(Gamma)$). Если $S subset T subset L$, то, пользуясь
      инвариантностью относительно $phi$ включения $N_T supset N_S inter N_L$,
      получим $N_(T') supset N_(S') inter N_(L')$, откуда
      $S' supset T' supset L'$ или $S' subset T' subset L'$. Фиксируя два из
      трех отрезков $S, T, L in tilde(Gamma)$, а третий изменяя в
      $tilde(Gamma)$, легко получаем, что $'$ есть автоморфизм или #source(
        9,
        printed: 638,
      ) антиавтоморфизм цепи $tilde(Gamma)$. Идеалы $N_(p p)$ и $N_(q q)$ при
      $p, q in Gamma$ по модулю $Z'_3$ соответственно инвариантны относительно
      $phi$ или меняются местами. Пусть $i in Gamma$, $p < i < q$. Определим
      отрезки $L, T$ условием $overline(L) inter T = {i}$. Тогда $L$ есть
      предшественник $T$ в цепи $tilde(Gamma)$ и
      $〈N_T, N_L〉 = N_(overline(L) T) = N_(i i)$. Если $'$ — автоморфизм цепи
      $tilde(Gamma)$, то $L'$ является предшественником $T'$ в цепи
      $tilde(Gamma)$ и, следовательно, существует $i' in Gamma$, для которого
      $overline(L') inter T' = {i'}$,
      $〈N_(T'), N_(L')〉 = N_(overline(L') T') = N_(i' i')$. Если $'$ —
      антиавтоморфизм, то $overline(T') inter L' = {i'}$,
      $〈N_(T'), N_(L')〉 = N_(overline(T') L')$. Таким образом, в обоих случаях
      существует подстановка $'$ цепи $Gamma$, являющаяся ее автоморфизмом или
      антиавтоморфизмом, для которой $N_(i i)^phi = N_(i' i')$ при $p < i < q$;
      в оставшихся случаях это равенство выполняется по модулю $Z'_3$.],

    [Допустим, $'$ — антиавтоморфизм цепи $Gamma$. Тогда
      $N_(i j)^phi = N_(i i)^phi inter N_(j j)^phi = N_(j' i')$,
      $p < j < i < q$, а поскольку $Q_(i j)$ совпадает со взаимным коммутантом
      $N_(i j)$ и $R$, то $Q_(i j)^phi = Q_(j' i')$, и для некоторых
      $theta_(i j) in Aut K^+$ имеем
      $(x epsilon_(i j))^phi = -x^(theta_(i j)) epsilon_(j' i')$
      ($mod Q_(j' i')$), $x in K$. Если $p ≪ i$ и не существует $m$,
      $p ◁ m ◁ i$, то эти равенства верны и при $j = p$; аналогично
      рассматривается случай $i = q$. В оставшихся случаях равенства верны по
      модулю $Q_(j' i') + Z'_3$. Коммутаторные соотношения между элементарными
      матрицами дают $(x y)^(theta_(i k)) = y^(theta_(m k)) x^(theta_(i m))$
      ($x, y in K$, $i > m > k$). Полагая $1^(theta_(i j)) = c_(i j)$, получаем
      $K^(theta_(i k)) = c_(m k) K^(theta_(i m)) = K^(theta_(m k)) c_(i m)$,
      откуда вытекает обратимость элементов $c_(i j)$ ($i > j$) в кольце $K$.
      Зафиксируем $m in Gamma$. С точностью до умножения $phi$ на диагональный
      автоморфизм можно считать, что $c_(m k) = c_(i m) = 1$. Инвариантность
      коммутаторных соотношений дает $c_(i j) = 1$ для всех $i, j in Gamma$,
      $i > j$. В этом случае все отображения $theta_(i j)$ совпадают,
      $theta_(i j) = theta$ ($i > j$) и $theta$ есть антиавтоморфизм кольца $K$.
      Умножая $phi$ на антисдвиг, приходим к равенству

      $
        (x epsilon_(i j))^phi = x epsilon_(i j) quad (mod Q_(i j)),
        quad x in K, i > j,
      $ <eq:l1987-rings-normalized>

      при $j != p$, $i != q$. Когда $'$ — автоморфизм цепи $Gamma$, к этому
      условию приходим, умножая $phi$ на диагональный, кольцевой автоморфизмы и
      на сдвиг. В исключительных случаях, когда
      $N_(m p)^phi = M_(m t)(frak(N))$, $p ◁ m ◁ t < q$ (здесь $2K = 0$), или
      $N_(m p)^phi = M_m lr((frak(M)))$, $p ◁ m$, по доказанному, #source(
        10,
        printed: 639,
      ) автоморфизм $phi$ действует на $N_(m p)$ тождественно по модулю
      коммутанта $R^2$ и (в силу абелевости идеала $N_(m p)^phi$) совпадает с
      $nu_a$ по модулю $Q_(m p) + N_(q m)$ или соответственно с $sigma_a$ по
      модулю $Q_(m p)$. Если $phi in Aut cal(G)(R)$, то, как и в
      [@bib:l1987-rings-Levchuk1983, леммы @lem:l1983-extremal-parameters и
      @lem:l1983-central-parameter-functions], доказывается существование
      автоморфизма $eta_a$ и соответственно $sigma_lambda$,
      $a = 2^lambda - 2(1^lambda)$. Умножая $phi$ на гиперцентральный
      автоморфизм, можем получить сейчас условие @eq:l1987-rings-normalized при
      $j = p$ и, аналогично, при $i = q$.],

    [Автоморфизм $phi$ с условием @eq:l1987-rings-normalized оставляет на месте
      идеалы $N_(i j)$ ($i > j$) и, следовательно, аддитивен на них. При
      $alpha in N_(i j)$, $beta in N_(k m)$, $i <= k$, имеем
      $N_(i j) N_(k m) = 0$ и, следовательно,
      $alpha^phi beta^phi = 0 = (alpha beta)^phi$; с другой стороны,
      $beta^phi alpha^phi$ совпадает и с $beta^phi * alpha^phi$, и с
      коммутатором $[beta^phi, alpha^phi]$, откуда
      $beta^phi alpha^phi = (beta alpha)^phi$. Поэтому ограничение $phi$ на
      элементарных матрицах сохраняет основные соотношения между ними в кольце
      $R$ и, следовательно, допускает продолжение до автоморфизма $R$. Отсюда
      $phi in Aut R$.],

    [Для фиксированного $i in Gamma$ соотношения
      $epsilon_(i j)^phi epsilon_(j m)^phi = epsilon_(i m)^phi$ показывают, что
      $j$-й столбец в $epsilon_(i j)^phi$ не зависит от выбора $j in Gamma$,
      $j < i$, и содержит лишь конечное число ненулевых элементов; отождествим
      его с $i$-м столбцом $Gamma$-матрицы $alpha = ‖a_(u v)‖$. Аналогично,
      $i$-ю строку в $epsilon_(i j)^phi$ отождествляем с $j$-й строкой
      $Gamma$-матрицы $alpha' = ‖a'_(u v)‖$. При $p in Gamma$ в $alpha$ остается
      определить $p$-й столбец, а в $alpha'$ при $q in Gamma$ — $q$-ю строку.
      Положим $a_(p p) = a'_(q q) = 1$. По построению, $(k,m)$-координаты
      произведений $alpha' alpha$ и $epsilon_(u k)^phi times epsilon_(m v)^phi$,
      $p < m < k < q$, совпадают, откуда $alpha' alpha = 1$ по модулю
      $D = N_(p p) + N_(q q)$. Кроме того,
      $alpha epsilon_(i j) alpha' = epsilon_(i j)^phi$ по модулю $D + N'_(i j)$,
      $N'_(i j) = 〈K epsilon_(u v) | v < j < i < u〉$. Отсюда
      $alpha = alpha(phi)$ совпадает по модулю $D$ с $alpha'(phi^(-1))$ и
      $alpha'(phi)$ — с $alpha(phi^(-1))$. В частности, $Gamma$-матрицы $alpha$
      и $alpha'$ имеют конечное число ненулевых элементов в каждом столбце,
      исключая, быть может, $p$-й при $p in Gamma$, и в каждой строке, исключая,
      быть может, $q$-ю при $q in Gamma$. Поэтому равенства

      $
        a_(k p) = -a'_(k p) - sum_(p<l<k) a'_(k l) a_(l p),
        quad a'_(q m) = -a_(q m) - sum_(m<l<q) a'_(q l) a_(l m)
      $

      определяют элементы $a_(k p)$ ($p < k < q$) и $a'_(q m)$ ($p < m < q$),
      причем $alpha' alpha = alpha alpha' = 1$ по модулю центра кольца $R$. С
      точностью до умножения $phi$ на локально внутренний автоморфизм можем
      считать, что по модулю центра $alpha = alpha' = 1$ и, следовательно,
      $epsilon_(i j)^phi = epsilon_(i j) + alpha_(i j)$, $i > j$, где #source(
        11,
        printed: 640,
      ) $alpha_(i j) in N'_(i j)$. Отсюда при $i > k > j$ получаем

      $
        epsilon_(i j)^phi = (epsilon_(i k) + alpha_(i k))
        (epsilon_(k j) + alpha_(k j)) = epsilon_(i j).
      $

      Кроме того, $alpha_(i j)$ при $p < j ◁ i < q$ имеет нулевыми все строки
      (аналогично, столбцы), исключая, быть может, $q$-ю (соответственно $p$-й);
      например, для строк это следует из равенств

      $
        0 = epsilon_(s u)^phi epsilon_(i j)^phi = epsilon_(s u) alpha_(i j)
        + alpha_(s u) epsilon_(i j), quad s > u > i > j.
      $

      Пользуясь сейчас равенствами

      $
        (x epsilon_(s u) epsilon_(i j))^phi
        = (x epsilon_(s u))^phi epsilon_(i j)
        = epsilon_(s u)(x epsilon_(i j))^phi
      $

      (см. также лемму @lem:l1983-central-ring-automorphisms
      [@bib:l1987-rings-Levchuk1983]), получаем, что $phi$ — центральный
      автоморфизм, описанный в § @sec:l1987-rings-automorphism-types. Это
      завершает доказательство теоремы.],
  )]

Группа $cal(G)(NT(n, K))$ изоморфна унитреугольной группе $UT(n, K)$.
Автоморфизмы последней были описаны в [@bib:l1987-rings-Pavlov1952;
@bib:l1987-rings-Weir1955; @bib:l1987-rings-Gibbs1970] для поля $K$
характеристики $!= 2$, а затем для произвольного кольца $K$ с единицей
[@bib:l1987-rings-Levchuk1975] (с полными доказательствами — в
[@bib:l1987-rings-Levchuk1983]); случай $K = GF(2^m)$ см. также
[@bib:l1987-rings-McBride1983]. Следствием частного случая теоремы
@th:l1987-rings-automorphisms, когда $Gamma$ — цепь натуральных чисел, $K$ —
конечное поле (здесь $Aut cal(G)(R)$ порождается диагональными, кольцевыми и
локально внутренними автоморфизмами), является основная теорема 1
[@bib:l1987-rings-Kosman1982]. (Отметим, что в [@bib:l1987-rings-Kosman1982]
ошибочно используются автоморфизмы, индуцированные автоморфизмами аддитивной
группы поля (см. [@bib:l1987-rings-Levchuk1975, замечание 1]); как показывает
предложение @prop:l1987-rings-ideal-criterion, исправления в
[@bib:l1987-rings-Kosman1982] требует также теорема 2 вместе с утверждением 1.3,
б).)

=== <sec:l1987-rings-characteristic>

Пусть $Omega$ — совокупность идеалов кольца $R = NT(Gamma, K)$, порождающихся
идеалами вида $N_(i j)$, $i > j$, и инвариантных относительно всех сдвигов и
фиксированного антисдвига $tau$ кольца $Lambda(R)$; если антисдвиг не
существует, полагаем $tau = 1$. Из теоремы @th:l1987-rings-automorphisms,
предложения @prop:l1987-rings-ideal-criterion и следствия из теоремы
@th:l1987-rings-normal-lie вытекает

#theorem[Пусть $K$ — тело, $|Gamma| > 4$. При $|K| > 2$ класс $Omega_pi$
  характеристических подгрупп группы $cal(G)(R)$ совпадает с $Omega$, за
  исключением случая, когда $K$ — поле характеристики $!= 2$, $Gamma$ — цепь без
  антиавтоморфизмов, $p, q in Gamma$ и существует $i in Gamma$, $p ◁ i$, или
  $i ◁ q$ (здесь $Omega_pi$ состоит из идеалов $H in Omega$, для которых
  $N_(q i) subset H$ при $H_(i p) != 0$, $p ◁ i$, и $N_(i p) subset H$ при
  $H_(q i) != 0$, $i ◁ q$). При $K = GF(2)$ класс $Omega_pi$ состоит из идеалов
  $H$ кольца #source(12, printed: 641) $Lambda(R)$, инвариантных относительно
  сдвигов и $tau$, причем, если $tau = 1$, $p, q in Gamma$, то при
  $p ◁ j ◁ i < q$ на $H$ накладывается условие $N_(q i) subset H$, когда
  $H_(j p) != 0$, и $N_(q j) subset H$, когда $H_(j p) = 0$, $H_(i p) != 0$, а
  при $p < j ◁ i ◁ q$ $N_(j p) subset H$, когда $H_(q i) != 0$, и
  $N_(i p) subset H$, когда $H_(q i) = 0$,
  $H_(q j) != 0$.] <th:l1987-rings-characteristic-subgroups>

Аналогично описываются характеристические идеалы кольца $Lambda(R)$.

