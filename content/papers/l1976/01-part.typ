#import "defs.typ": *
#import "../../statements.typ": *

#heading(level: 3, numbering: none)[Введение] <sec:l1976-introduction>

#source(2, printed: 558)Пусть $K$ — произвольное ассоциативное кольцо.
Унитреугольная группа $UT(n, K)$ изоморфна присоединенной группе по умножению
$alpha compose beta = alpha + beta + alpha beta$ кольца $NT(n, K)$ матриц
степени $n$ над $K$ с нулями на и над главной диагональю; изоморфизмом служит
отображение $alpha arrow.r alpha + epsilon$, $alpha in NT(n, K)$, где $epsilon$
— единичная матрица. С кольцом $NT(n, K)$ ассоциировано также кольцо Ли,
получающееся заменой обычного умножения матриц на лиево:
$alpha ast beta = alpha beta - beta alpha$.

Известно [@bib:l1976-Malcev1949], что во всяком нильпотентном ассоциативном
кольце идеалы являются одновременно нормальными подгруппами присоединенной
группы. Для некоторых колец $NT(n, K)$ это утверждение частично обращалось
автором (см. [@bib:l1976-Levchuk1974], следствие @cor:l1974-normal-subrings).
Ниже найдено точное соответствие: класс нормальных подгрупп присоединенной
группы кольца $NT(n, K)$ при $K = K^2$ совпадает с классом идеалов лиева кольца
$NT(n, K)$ (теорема~@th:l1976-normal-lie-correspondence). Отсюда, в частности,
вытекает обобщение следствия @cor:l1974-normal-subrings из
[@bib:l1976-Levchuk1974]: нормальная подгруппа присоединенной группы кольца
$NT(n, K)$, $K = K^2$, является его подкольцом. Требование $K = K^2$ в этих
утверждениях при $n < 5$ излишне; при $n >= 5$ условие $K = K^2$ существенно,
как показывает пример~@exm:l1976-even-ring. (См. также
замечание~@rem:l1976-normal-groupoid-question.)

Вопрос об описании нормальных подгрупп группы $UT(n, K)$ при $K = K^2$
совпадает, по теореме~@th:l1976-normal-lie-correspondence, с вопросом об
описании идеалов лиева кольца $NT(n, K)$. Автор [@bib:l1976-Levchuk1974],
теорема @th:l1974-normal-description, описал нормальные подгруппы унитреугольной
группы над телом. Теорема~@th:l1976-lie-ideals содержит уточнение этого
результата #source(3, printed: 559)и имеет более простое доказательство. Ранее
Дюбиш и Перлис [@bib:l1976-Dubisch1951] описали идеалы алгебры $NT(n, K)$ над
полем $K$. В §~@sec:l1976-lie-ideals показано, что идеалы лиева кольца
$NT(n, K)$ допускают аналогичное описание, однако лишь при условии простоты
кольца $K$. В §~@sec:l1976-lie-ideals нормальные подгруппы присоединенной группы
кольца $NT(n, ZZ)$, как идеалы лиева кольца $NT(n, ZZ)$, предлагается выделять,
по лемме~@lem:l1976-integer-basis, в классе подгрупп аддитивной группы
$NT(n, ZZ)$. Описание последних хорошо известно в терминах баз, поскольку
аддитивная группа $NT(n, ZZ)$ является свободной абелевой группой конечного
ранга.

Доказывается, что класс $Omega(n, K)$ максимальных абелевых нормальных подгрупп
присоединенной группы кольца $NT(n, K)$ всегда совпадает с классом максимальных
абелевых идеалов лиева кольца $NT(n, K)$; для первичного кольца $K$ он шире
класса максимальных абелевых идеалов кольца $NT(n, K)$ лишь при условии
$2K = 0$, $n > 3$. Для первичного кольца $K$ лемма~@lem:l1976-prime-abelian
указывает запись в явном виде максимальных абелевых идеалов кольца $NT(n, K)$ и
ассоциированного кольца Ли. Полное их описание дается
теоремой~@th:l1976-maximal-abelian в случае, когда кольцо $K$ вложимо в тело.
Как частный случай отсюда вытекает теорема 6 Уира [@bib:l1976-Weir1955],
описывающая максимальные абелевы нормальные подгруппы унитреугольной группы над
конечным полем нечетной характеристики.

О результатах настоящей статьи сообщалось в [@bib:l1976-Levchuk1976]. Во второй
части работы будет дано описание автоморфизмов кольца $NT(n, K)$, его
присоединенной группы и ассоциированного кольца Ли.

=== #[Соответствия между нормальными подгруппами присоединенной группы кольца
  $NT(n, K)$ и идеалами ассоциированного кольца Ли]
<sec:l1976-correspondence>

Основным результатом параграфа является

#theorem[
  Пусть $K$ есть произвольное ассоциативное кольцо. Класс максимальных абелевых
  нормальных подгрупп присоединенной группы кольца $NT(n, K)$ совпадает с
  классом максимальных абелевых идеалов ассоциированного #source(
    4,
    printed: 560,
  )кольца Ли. При $K = K^2$ класс всех нормальных подгрупп присоединенной группы
  совпадает с классом всех идеалов лиева кольца $NT(n, K)$.
] <th:l1976-normal-lie-correspondence>

#proof[
  Введем обозначение $epsilon_(i j)$ для квадратной матрицы степени $n$, у
  которой $(i, j)$-координата равна единице (быть может, формальной), а все
  остальные равны нулю. Матрицы $x epsilon_(i j)$, $x in K$, называются
  элементарными. Они умножаются по следующему правилу:
]
$
  (x epsilon_(i j))(y epsilon_(k m)) = cases(
    x y epsilon_(i m)\, & j = k,
    0\, & j != k,
  ), quad x, y in K.
$ <eq:l1976-elementary-product>

#lemma[
  Аддитивная и присоединенная группы кольца $NT(n, K)$ порождаются своими
  элементарными матрицами.
] <lem:l1976-elementary-generators>

#proof[
  Если $lr(‖a_(i j)‖) in NT(n, K)$, то ввиду @eq:l1976-elementary-product имеем
  $
    lr(‖a_(i j)‖) & = sum_(i > j) a_(i j) epsilon_(i j)
                    = a_21 epsilon_21 compose \
                  & quad a_31 epsilon_31 compose a_32 epsilon_32 compose \
                  & quad dots \
                  & quad compose a_(n 1) epsilon_(n 1) compose
                    a_(n 2) epsilon_(n 2) compose dots compose
                    a_(n,n - 1) epsilon_(n,n - 1).
  $
]

#lemma[
  Совокупность $N_(k m)$, $1 <= m < k <= n$, всех матриц из $NT(n, K)$ с нулями
  выше $k$-й строки, а также в столбцах, номера которых больше $m$, есть идеал
  кольца $NT(n, K)$. Умножение в идеале $N_(k m)$ есть нулевое, и,
  следовательно, присоединенное умножение совпадает со сложением.
] <lem:l1976-rectangle-ideal>

#proof[также следует из @eq:l1976-elementary-product.]

Основной леммой в доказательстве теоремы~@th:l1976-normal-lie-correspondence
является

#lemma[
  Подгруппа $H$ присоединенной #source(5, printed: 561)группы кольца $NT(n, K)$
  нормальна тогда и только тогда, когда $H$ является идеалом группоида
  $NT(n, K)$ относительно лиева умножения $ast$. Кроме того, из нормальности $H$
  вытекает включение $H supset.eq H + H_1$, где $H_1$ есть идеал кольца
  $NT(n, K)$, порожденный множеством $H ast NT(n, K)$.
] <lem:l1976-normal-groupoid>

#proof[
  Прежде всего установим соотношения, связывающие коммутирование в
  присоединенной группе кольца $NT(n, K)$ с лиевым умножением $ast$. Через
  $alpha'$ будем обозначать элемент, обратный к $alpha$ в присоединенной группе:
  $alpha + alpha' + alpha alpha' = 0$. Пусть $alpha, beta in NT(n, K)$. Тогда
  $
    [alpha, beta] & = (alpha' compose beta') compose (alpha compose beta) \
                  & = lr(
                      [
                        -beta compose alpha
                        - (beta compose alpha)' (beta compose alpha)
                      ]
                    )
                    + alpha compose beta \
                  & quad + (alpha' compose beta')(alpha compose beta)
                    = alpha ast beta + (alpha' compose beta')(alpha ast beta) \
                  & = alpha ast beta + alpha'(alpha ast beta)
                    + (beta' + alpha' beta')(alpha ast beta).
  $

  Если $beta$ — элементарная матрица, то, по лемме~@lem:l1976-rectangle-ideal,
  матрицы $beta$ и $beta'$ содержатся в идеале кольца $NT(n, K)$ с нулевым
  умножением. Поэтому из предыдущих равенств вытекает
  $
    [alpha, x epsilon_(k m)] = alpha ast x epsilon_(k m)
    + alpha'(alpha ast x epsilon_(k m)), quad k > m, quad x in K.
  $ <eq:l1976-elementary-commutator>

  Используя @eq:l1976-elementary-commutator, @eq:l1976-elementary-product и
  вновь лемму~@lem:l1976-rectangle-ideal, приходим к следующим равенствам при
  $i > ell > j$:
  $
    [[x epsilon_(i ell), alpha], y epsilon_(ell j)]
    = (alpha' ast x epsilon_(i ell)) ast y epsilon_(ell j)
    = alpha' x y epsilon_(i j),
  $ <eq:l1976-double-commutator-left>
  $
    [x epsilon_(i ell), [alpha, y epsilon_(ell j)]]
    = x epsilon_(i ell) ast (alpha ast y epsilon_(ell j))
    = -x y epsilon_(i j) alpha.
  $ <eq:l1976-double-commutator-right>

  Пусть $H$ — нормальная подгруппа присоединенной группы. В силу
  @eq:l1976-double-commutator-left и того, что присоединенное умножение в идеале
  $N_(k m)$ совпадает со сложением, пересечение $H inter N_(k m)$ содержит
  матрицы $alpha'(alpha ast x epsilon_(k m))$, а следовательно, и матрицы
  $
    alpha ast x epsilon_(k m)
    = [alpha, x epsilon_(k m)] compose
    (-alpha'(alpha ast x epsilon_(k m)))
  $
  при любых $alpha in H$, $x in K$, $k > m$. Таким образом, нормальная подгруппа
  $H$ замкнута относительно лиева умножения своих элементов #source(
    6,
    printed: 562,
  )на элементарные матрицы. Покажем, что для любых матриц
  $alpha = lr(‖a_(i j)‖)$ и $beta = lr(‖b_(i j)‖)$ из $H$ справедливо включение:
  $
    H in.rev alpha + beta ast x epsilon_(k m)
    = (beta ast x epsilon_(k m)) compose alpha
    - (beta ast x epsilon_(k m)) alpha.
  $
  Матрица $(beta ast x epsilon_(k m)) alpha$ равна нулю при $m = 1$, ввиду
  @eq:l1976-elementary-product, а при $m > 1$ разложима в сумму матриц вида
  $delta ast y epsilon_(s t)$, где $delta in H$, $y in K$, $t < m$.
  Существование такого разложения следует из равенств:
  $
    beta x epsilon_(k m) alpha
    = sum_(j = 1)^(m - 1) (beta ast x epsilon_(k m))
    ast a_(m j) epsilon_(m j),
  $
  $
    x epsilon_(k m) beta alpha
    = sum_(j = 1)^(m - 1) (alpha ast x epsilon_(k m))
    ast b_(m j) epsilon_(m j)
    - sum_(j = 1)^(m - 1) alpha ast x b_(m j) epsilon_(k j),
  $
  которые устанавливаются с помощью @eq:l1976-double-commutator-left,
  @eq:l1976-double-commutator-right и тождества Якоби. Поэтому искомое включение
  получается сейчас индукцией по $m$. Из него вытекает включение:
  $H supset.eq H + H_1$, где $H_1$ есть идеал лиева кольца $NT(n, K)$,
  порожденный множеством $H ast NT(n, K)$. В силу @eq:l1976-elementary-product,
  @eq:l1976-double-commutator-left, @eq:l1976-double-commutator-right $H_1$ есть
  также идеал кольца $NT(n, K)$.

  Пусть сейчас $H$ есть подгруппа присоединенной группы, которая является
  идеалом группоида $lr(⟨NT(n, K); ast⟩)$. Покажем, что она является нормальной
  подгруппой. Для этого, по лемме~@lem:l1976-elementary-generators, достаточно
  доказать, что $H$ содержит матрицы @eq:l1976-elementary-commutator при
  $alpha in H$. Зафиксируем матрицу $x epsilon_(k m)$. Пересечение
  $H inter N_(k m)$ в силу @eq:l1976-double-commutator-left содержит матрицы
  вида $alpha'(x epsilon_(k m))(y epsilon_(m j))$ или
  $alpha'(y epsilon_(i k))(x epsilon_(k m))$, а также их всевозможные суммы, в
  частности, $alpha'(alpha ast x epsilon_(k m))$, так как присоединенное
  умножение в идеале $N_(k m)$ совпадает со сложением. Отсюда и из
  @eq:l1976-elementary-commutator следует, что коммутатор
  $[alpha, x epsilon_(k m)]$ содержится в $H inter N_(k m)$.

  Лемма доказана.
]

#lemma[
  Пусть $H$ — абелев идеал кольца Ли $NT(n, K)$ или абелева нормальная подгруппа
  присоединенной группы кольца $NT(n, K)$. Тогда множество
  $H dot NT(n, K) H + H^2$ содержится в аннуляторе кольца $NT(n, K)$. Кроме
  того,
  $
    alpha gamma beta + beta gamma alpha = 0,
    quad alpha, beta in H, quad gamma in NT(n, K).
  $
] <lem:l1976-abelian-annihilator>

#proof[
  #source(7, printed: 563)Выберем произвольные матрицы $alpha, beta in H$ и
  элементарную матрицу $x epsilon_(i j) equiv gamma$, $i > j$, $x in K$. По
  условию и по лемме~@lem:l1976-normal-groupoid, матрица $beta ast gamma$
  содержится в $H$ и, следовательно, перестановочна с $alpha$, т.~е.
  $
    alpha beta gamma + gamma beta alpha
    - (alpha gamma beta + beta gamma alpha) = 0.
  $
  В силу выбора $gamma$ у матрицы в скобках $i$-я строка и $j$-й столбец
  являются нулевыми. В то же время матрицы $alpha beta gamma$ и
  $gamma beta alpha$ могут иметь ненулевые элементы лишь в $j$-м столбце и $i$-й
  строке соответственно, исключая позицию $(i, j)$. Поэтому равенство дает:
  $
    alpha beta gamma = gamma beta alpha
    = alpha gamma beta + beta gamma alpha = 0,
    quad alpha, beta in H.
  $
  Справедливость этих равенств для произвольной матрицы $gamma$ кольца
  $NT(n, K)$ вытекает сейчас из того, что его аддитивная группа порождается
  элементарными матрицами. Таким образом, аннулятор кольца $NT(n, K)$ содержит
  множество $H^2$, а ввиду равенств
  $
    alpha(gamma ast beta) = alpha gamma beta - alpha beta gamma
    = alpha gamma beta,
    quad alpha, beta in H, quad gamma in NT(n, K),
  $
  содержит также множество $H dot NT(n, K) H$.

  Лемма доказана.
]

#metadata((kind: "passage")) <pass:l1976-adjoint-additive-closure>
Пусть $H$ — максимальная абелева нормальная подгруппа присоединенной группы
кольца $NT(n, K)$. Ясно, что $H$ содержит аннулятор кольца $NT(n, K)$, а
следовательно, и $H^2$, в силу леммы~@lem:l1976-abelian-annihilator.
Следовательно, $H$ содержит матрицы
$alpha - beta = alpha compose beta' compose (beta beta' - alpha beta')$
при всех $alpha, beta in H$ ($beta compose beta' = 0$). Поэтому $H$ является
аддитивной группой, а в силу леммы~@lem:l1976-normal-groupoid и идеалом лиева
кольца $NT(n, K)$. Обратно: пусть $H$ — максимальный абелев идеал лиева кольца
$NT(n, K)$. Множество $H^2$ содержится в аннуляторе кольца $NT(n, K)$ по
лемме~@lem:l1976-abelian-annihilator, а потому и в $H$. Отсюда $H$ есть
подкольцо кольца $NT(n, K)$, а следовательно, и подгруппа присоединенной группы.
Подгруппа $H$ нормальна по лемме~@lem:l1976-normal-groupoid и абелева в силу
того, что условия абелевости множества $H subset.eq NT(n, K)$ относительно
обычного умножения матриц, относительно лиева умножения и относительно
присоединенного умножения совпадают. Тем самым доказано первое утверждение
теоремы~@th:l1976-normal-lie-correspondence.

Допустим сейчас, что аддитивная группа кольца $K$ порождается #source(
  8,
  printed: 564,
)элементами $a b$, $a,b in K$ (кратко: $K = K^2$).
<pass:l1976-lie-products>
Докажем, что в этом случае для любых двух матриц $alpha = lr(‖a_(i j)‖)$ и
$beta = lr(‖b_(i j)‖)$ из кольца $NT(n, K)$ идеал $M(alpha, beta)$
ассоциированного кольца Ли, порожденный множеством
$lr({alpha, beta}) ast NT(n, K)$, содержит произведение $alpha beta$. С этой
целью индукцией по $ell$ будем доказывать включения
$
  (alpha, beta)_(n - ell)
  equiv sum_(j = n - ell)^(n - 1) alpha
  (b_(j + 1,j) epsilon_(j + 1,j)) in M(alpha, beta),
$
$ell = 1, 2, dots, n - 1$. Матрицы $(alpha, beta)_(n - 1)$ и
$(beta, alpha)_(n - 1)$ являются нулевыми и, следовательно, содержатся в
$M(alpha, beta)$. Пусть $1 <= k < n - 1$, и допустим, что включение
$(alpha, beta)_(k + 1), (beta, alpha)_(k + 1) in M(alpha, beta)$ уже доказано.
Справедливы равенства:
$
  (beta, alpha)_(k + 1)
  &= (beta, alpha)_(k + 1)
  + alpha (sum_(j = k + 1)^(n - 1) sum_(ell = 1)^(j - 1)
    b_(j ell) epsilon_(j ell))
  - (sum_(i = k + 2)^n sum_(j = k + 1)^(i - 1)
    a_(i j) epsilon_(i j)) beta \
  &= (alpha, beta)_k
  + sum_(j = k + 1)^(n - 1) sum_(ell = 1)^(j - 2)
  alpha b_(j ell) epsilon_(j ell)
  - sum_(i = k + 3)^n sum_(j = k + 1)^(i - 2)
  a_(i j) epsilon_(i j) beta \
  &quad + [(beta, alpha)_(k + 1)
    - sum_(j = k + 1)^(n - 1) a_(j + 1,j) epsilon_(j + 1,j) beta].
$
Слагаемое в квадратных скобках совпадает с суммой
$
  sum_(j = k + 1)^(n - 1) beta ast
  a_(j + 1,j) epsilon_(j + 1,j)
$
и, следовательно, содержится в $M(alpha, beta)$ по определению. Так как
$K = K^2$, то существуют элементы $x_t, y_t in K$ такие, что
$a_(i j) = sum_t x_t y_t$. Поэтому при $i - j > 1$ матрица
$
  a_(i j) epsilon_(i j) beta
  = (sum_t x_t y_t) epsilon_(i j) beta
  = sum_t (x_t epsilon_(i ell))(y_t epsilon_(ell j)) beta
$
$(i > ell > j)$ содержится в идеале $M(alpha, beta)$ в силу
@eq:l1976-double-commutator-right. Аналогично матрица
$alpha b_(j ell) epsilon_(j ell)$ содержится в идеале $M(alpha, beta)$ при
$j - ell > 1$. Таким образом,
$(beta, alpha)_(k + 1) in (alpha, beta)_k + M(alpha, beta)$, откуда
$(alpha, beta)_k in M(alpha, beta)$. В силу произвольности матриц $alpha$ и
$beta$ также имеем: $M(alpha, beta) = M(beta, alpha) supset.eq (beta, alpha)_k$.
