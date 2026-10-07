#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

#heading(level: 3, numbering: none)[Введение] <sec:l1982-parabolic-introduction>

#source(2, printed: 509)Пользуясь существованием $(B,N)$-пары в группе Шевалле
над полем, Титс [@bib:l1982-parabolic-Tits1962] описал (наряду с доказательством
абнормальности) её параболические подгруппы. Поискам подобных описаний в группе
Шевалле над кольцом $K$, когда подход Титса применить не удаётся, посвящён ряд
работ, в значительной степени инспирированных работой
[@bib:l1982-parabolic-Newman1959] (подробнее см.
§~@sec:l1982-parabolic-comparison).
Теорема~@th:l1982-parabolic-normal-basis-decomposition приводит к единообразному
доказательству полученных в них результатов, причём в большей общности (см.
теоремы~@th:l1982-parabolic-diagonal-overgroups и
@th:l1982-parabolic-unipotent-overgroups). В частности, снимаются ограничения на
характеристику кольца $K$. Применения
теоремы~@th:l1982-parabolic-normal-basis-decomposition к группам Шевалле
основываются на лемме~@lem:l1982-parabolic-root-isolation, усиливающей одну
лемму Шевалле [@bib:l1982-parabolic-Chevalley1958], и на
лемме~@lem:l1982-parabolic-root-folding. Дальнейшее развитие нашли понятия ковра
и ковровой подгруппы, введённые Ю.~И.~Мерзляковым
[@bib:l1982-parabolic-Merzlyakov1964]. Результаты статьи анонсировались
[@bib:l1982-parabolic-Levchuk1980].

=== #[ ] <sec:l1982-parabolic-normal-bases>

Набор $Omega={X_1,X_2,dots,X_n}$ подмножеств группы $B$ назовём её нормальным
базисом, если выполнены условия:
#enum(
  numbering: n => "Б" + str(n) + ")",
  [$X^((i))=X_(i+1) X_(i+2) dots X_n$, $0<=i<=n$ ($X^((n))=1$) — нормальные
    подгруппы в $B$;],
  [элементы из $X^((0))$ записываются в виде $x_1 x_2 dots x_n$ ($x_i in X_i$)
    единственным способом;],
  [$X^((0))=B$.],
)
Нормальный базис нильпотентной группы Ли, составленный из однопараметрических
подгрупп, рассматривал А.~И.~Мальцев [@bib:l1982-parabolic-Malcev1949], называя
его системой координат 2-го рода (см. также понятие мальцевской базы
[@bib:l1982-parabolic-Merzlyakov1968; @bib:l1982-parabolic-Kargapolov1977]).

#theorem[
  Пусть $Gamma$ — группа, $D subset Aut Gamma$, $B$ — подгруппа с нормальным
  базисом $Omega={X_1,X_2,dots,X_n}$, #source(3, printed: 510)причём все
  подгруппы $X^((i))$ ($0<=i<=n$) $D$-допустимы и
  $
    lr(chevron.l [D_j,a]^D chevron.r) X^((j)) ∋ a
    quad (a in X_i, quad 1<=i<j<=n),
  $ <eq:l1982-parabolic-extraction-condition>
  где $D_j={phi in D | [phi,X_j] subset X^((j))}$. Тогда:
  #enum(
    numbering: ru-enum,
    [для всякой $D$-допустимой подгруппы $M subset Gamma$ пересечения
      $M inter X_1,dots,M inter X_n$ образуют нормальный базис $M inter B$;],
    [если $lr(chevron.l [D,a]^D chevron.r) ∋ a$ при $a in X_n$, то всякая
      подгруппа $A$, для которой $Gamma=A B A$ и $D$ есть подгруппа группы
      сопряжений элементами из $A$, абнормальна в $Gamma$.],
  )
] <th:l1982-parabolic-normal-basis-decomposition>

#proof[
  а) Допустим, что произведение $x_1 x_2 dots x_r$, где $x_i in X_(alpha_i)$,
  $1<=alpha_1<alpha_2<dots<alpha_r<=n$, лежит в $M$. Покажем, что и сомножители
  лежат в $M$. Пусть $r>1$. Тогда
  $
    [phi,x]=x^phi x^(-1)
    =x_1^phi x_2^phi dots x_r^phi x_r^(-1) dots x_2^(-1) x_1^(-1)
    =[phi,x_1] mod X^((alpha_2)) quad (phi in D_(alpha_2)),
  $
  и поэтому $[D_(alpha_2),x_1] subset (B inter M) X^((alpha_2))$. Отсюда и в
  силу @eq:l1982-parabolic-extraction-condition существует $y in X^((alpha_2))$,
  при котором $x_1 y in B inter M$. Индукция по $n-alpha_2$ доказывает включение
  $x_1 in M$, а индукция по $r$ — включения $x_i in M$. Отсюда вытекает а). В
  случае б) покажем, что для любого $x in Gamma=A B A$ подгруппа
  $M=lr(chevron.l A, A^x chevron.r)$ содержит $x$. Так как $M supset A$, то
  можно считать, что $x=x_1 y$, $x_1 in X_alpha$, $y in X^((alpha))$ для
  некоторого $alpha$, $1<=alpha<=n$. В силу выбора $D$ в б) справедливо
  включение $[D,x] subset M inter B$, а при $alpha=n$ также включение $x in M$.
  Как и в а), при $alpha<n$ находим $x_1 in B inter M$ и, кроме того,
  $
    [D,y] subset x_1^(-1) [x_1,D] [D,x] x_1 subset B inter M.
  $
  Индукция по $n-alpha$ завершает доказательство включения $x in M$.
  Следовательно, $A$ — абнормальная подгруппа в $Gamma$
  [@bib:l1982-parabolic-Shemetkov1978, 17.1]. Теорема доказана.
]

Свойство Б2) в доказательстве явно не использовалось. Однако когда $X_i$ —
подгруппы, оно легко следует из других условий. В самом деле, пусть $X_i$ —
подгруппы с условиями Б1), Б3), а $D$ выбирается так же, как и в
теореме~@th:l1982-parabolic-normal-basis-decomposition, а). Предположим, что Б2)
не выполняется и, следовательно, существуют индексы $i<j<=n$ и элемент
$a in X_i inter (X^((j-1)) without X^((j)))$. Но тогда
$[D_j,a] subset [D_j,X^((j-1))] subset X^((j))$ и в силу
@eq:l1982-parabolic-extraction-condition, $a in X^((j))$, вопреки выбору $a$.

Для набора $Omega={X_1,X_2,dots}$ подмножеств группы $B$ подгруппу $M$ называем
$Omega$-решёточной, если при $i_1<i_2<dots<i_r$ всегда имеем
$M inter (X_(i_1) dots X_(i_r))=(M inter X_(i_1)) #source(4, printed: 511)dots
(M inter X_(i_r))$; её назовём $Omega$-ковровой, если, кроме того,
$M=lr(chevron.l M inter X_1, M inter X_2, dots chevron.r)$. На связь этих двух
понятий указывает очевидная (как и лемма~@lem:l1982-parabolic-three-blocks)

#lemma[
  Пересечения $Omega$-решёточной подгруппы $M$ с каждым множеством из $Omega$
  порождают $Omega$-ковровую подгруппу $M_Omega$, и всякая подгруппа $H$,
  $M_Omega subset H subset M$, — $Omega$-решёточная.
] <lem:l1982-parabolic-lattice-subgroup>

#lemma[
  Допустим, что набор $Omega={X_1,dots,X_n}$ подмножеств группы удовлетворяет
  условию Б2) и $1<=k<n$. Тогда всякая подгруппа, решёточная относительно
  каждого из трёх наборов ${X_1 X_2 dots X_k,X_(k+1) X_(k+2) dots X_n}$,
  ${X_1,X_2,dots,X_k}$, ${X_(k+1),X_(k+2),dots,X_n}$, $Omega$-решёточна.
] <lem:l1982-parabolic-three-blocks>

Конечно, решёточность подгруппы сохранится, если заменить последовательность
$Omega$ на её подпоследовательность. С набором $Omega$, удовлетворяющим Б2),
будем ассоциировать частичные отображения $f_(i j;k):(X_i,X_j)->X_k$, обозначая
через $f_(i j;k) lr((a,b))$ при $(a,b) in (X_i,X_j)$ $k$-ю компоненту
коммутатора $[a,b]=a b a^(-1) b^(-1)$ в случае, когда он лежит в $X^((0))$.
Таким образом,
$
  [a,b]=f_(i j;1) lr((a,b)) f_(i j;2) lr((a,b)) dots
  f_(i j;n) lr((a,b)), quad (a,b) in (X_i,X_j).
$ <eq:l1982-parabolic-commutator-components>

#lemma[
  Пусть $B$ — группа с нормальным базисом $Omega={X_1,dots,X_n}$ и
  ассоциированными с ним отображениями $f_(i j;k)$, причём
  $[X_j,X_i] subset X^((i))$, $1<=i<j<=n$. Если подмножества $Y_i subset X_i$
  удовлетворяют условиям $f_(j i;k) lr((Y_j,Y_i)) subset Y_k$ ($1<=i<j<=n$,
  $i<k<=n$), $lr(chevron.l Y_i chevron.r) subset Y^((i-1))$ ($1<=i<=n$), то
  $Y^((0))$ — $Omega$-ковровая подгруппа. Все $Omega$-ковровые подгруппы группы
  $B$ получаются таким способом.
] <lem:l1982-parabolic-carpet-components>

Так как здесь $[Y_j,Y_i] subset Y^((i))$ ($1<=i<j<=n$), то
лемму~@lem:l1982-parabolic-carpet-components включает

#lemma[
  Пусть $B$ — группа с нормальным базисом $Omega={X_1,dots,X_n}$. Для
  $Omega$-решёточности её подгруппы $M$ необходимо и достаточно, чтобы
  пересечения $M inter X_1,dots,M inter X_n$ составляли в $M$ нормальный базис.
  В частности, свойства $Omega$-решёточности и $Omega$-ковровости подгрупп в $B$
  совпадают. Если подмножества $Y_i subset X_i$ таковы, что
  $[Y_j,Y_i] subset Y^((i))$ ($1<=i<j<=n$),
  $lr(chevron.l Y_i chevron.r) subset Y^((i-1))$ ($1<=i<=n$), то $Y^((0))$ —
  подгруппа с нормальным базисом $Y_1,Y_2,dots,Y_n$.
] <lem:l1982-parabolic-normal-basis-criterion>

#proof[
  Последнее утверждение леммы (оно инспирировано теоремой
  @th:l1974-layer-subgroup из [@bib:l1982-parabolic-Levchuk1974]) получаем,
  пользуясь включениями
  $
    #source(5, printed: 512)lr(chevron.l Y_k, Y_(k+1), dots, Y_n chevron.r)
    subset Y_k lr(chevron.l Y_(k+1), dots, Y_n chevron.r), quad 1<=k<=n.
  $
  Первое следует из определений.
]

Свойство решёточности подгруппы относительно нормального базиса $Omega$ не
зависит от выбора упорядочения в $Omega$. В силу предыдущей леммы это следует из
[@bib:l1982-parabolic-Steinberg1975, лемма 18], когда $X_i$ — подгруппы; общий
случай доказывается аналогично.

=== #[ ] <sec:l1982-parabolic-elementary-carpets>

Всюду в дальнейшем $Phi$ есть приведённая неразложимая система корней евклидова
пространства $cal(E)$, $Pi={p_1,p_2,dots,p_l}$ — её система простых корней.
Аддитивная подгруппа $L_0=L_0 lr((Phi))$, порождённая всеми корнями, содержится
в аддитивной подгруппе $L_1$, порождённой фундаментальными весами
$q_1,q_2,dots,q_l$, которые определяются условиями $(h_(p_i),q_j)=0$ при $i!=j$
и $1$ при $i=j$, $h_r=frac(2r, lr((r,r)))$ [@bib:l1982-parabolic-Bourbaki1972;
@bib:l1982-parabolic-Carter1972]. Как и в [@bib:l1982-parabolic-Steinberg1975,
§3], группой Шевалле $Phi(K)$ над коммутативным кольцом $K$ (ассоциативным и с
единицей) называем подгруппу $lr(chevron.l X_r | r in Phi chevron.r)$ группы
$GL(V^K)$, где $V^K$ есть $K$-модуль, определяемый через $Phi$ и группу весов
$L$, $L_0 subset L subset L_1$ (см. [@bib:l1982-parabolic-Steinberg1975, лемму
27 и замечание на стр. 42]), а $X_r$ — корневая подгруппа, являющаяся образом
аддитивной группы $K^+$ кольца $K$ при её изоморфизме $t->e_r lr((t))$
($t in K$) в $GL(V^K)$. (Группу Шевалле определяют ещё по групповой схеме
Шевалле — Демазура [@bib:l1982-parabolic-Demazure1970, XXIII], как надгруппу
группы $Phi(K)$, называя при этом последнюю элементарной подгруппой, например,
[@bib:l1982-parabolic-Stein1971].) Каждому $K$-характеру $chi$ группы $L_0$,
т.~е. её гомоморфизму в мультипликативную группу $K^hash$ кольца $K$,
сопоставляют ([@bib:l1982-parabolic-Chevalley1958, стр. 24], а также
[@bib:l1982-parabolic-Carter1972, §7.1]) элемент $h(chi) in GL(V^K)$. Функция
$h(chi)$ мультипликативна по $chi$, причём
$
  h(chi) e_r lr((t)) h(chi)^(-1)=e_r lr((chi(r)t))
  quad (r in Phi, quad t in K).
$ <eq:l1982-parabolic-diagonal-conjugation>

Элементы $h(chi)$, для которых $chi$ допускает продолжение до $K$-характера
группы $L$, $L_0 subset L subset L_1$, образуют подгруппу $H^L=H^L lr((K))$
группы $GL(V^K)$, и мы полагаем
$Phi^L lr((K))=lr(chevron.l Phi(K), H^L chevron.r)$ ($=Phi(K)H^L$). Подгруппа
$H=H^(L_1)$ порождается элементами $h(chi_(r,t))=h_r lr((t))$ ($r in Phi$,
$t in K^hash$) и содержится в $Phi(K)$ [@bib:l1982-parabolic-Carter1972, 7.1].
Включение $h(chi_(r,t)) in Phi(K)$ доказано в
[@bib:l1982-parabolic-Chevalley1958] для случая поля $K$ с использованием
гомоморфизма $SL_2 lr((K))->lr(chevron.l X_r, X_(-r) chevron.r)$, однако
доказательство остаётся справедливым и для кольца $K$, если группу
$SL_2 lr((K))$ заменить подгруппой
$lr(chevron.l t_(12) lr((K)), t_(21) lr((K)) chevron.r)$.

#source(6, printed: 513)Упорядочим набор $Omega$ корневых подгрупп $X_r$,
$r in Phi$, в соответствии с регулярным упорядочением корней
[@bib:l1982-parabolic-Chevalley1958, стр. 7]; все $Omega$-ковровые подгруппы
группы $Phi(K)$ назовём элементарно ковровыми. Формула
@eq:l1982-parabolic-commutator-components для выбранного $Omega$ превращается в
коммутаторную формулу Шевалле [@bib:l1982-parabolic-Chevalley1958, §3, (4)] (см.
также [@bib:l1982-parabolic-Steinberg1975; @bib:l1982-parabolic-Carter1972;
@bib:l1982-parabolic-Stein1971]). Последняя показывает, что для линейно
независимых корней $r,s in Phi$ подгруппы $X_(i r+j s)$ ($i r+j s in Phi$,
$i>0$, $j>0$) в порождённой ими подгруппе (аналогично, подгруппы $X_a$
($a in Phi^+$) в нижней унипотентной подгруппе
$U=lr(chevron.l X_a | a in Phi^+ chevron.r)$ и подгруппы $X_a$ ($a in Phi^-$) в
$U^-=lr(chevron.l X_a | a in Phi^- chevron.r)$) образуют нормальный базис.
Назовём элементарным ковром (типа $Phi$ над $K$) всякий набор
${frak(A)_r | r in Phi}$ аддитивных подгрупп кольца $K$ с условием
$
  C_(i j;r s) frak(A)_r^i frak(A)_s^j subset frak(A)_(i r+j s)
  quad (r,s,i r+j s in Phi, quad i>0, quad j>0),
$ <eq:l1982-parabolic-elementary-carpet-condition>
где $frak(A)_r^i={a^i | a in frak(A)_r}$, $C_(i j;r s)$ — константы из
коммутаторной формулы Шевалле. Его называем допустимым, если определяемая по
нему подгруппа $lr(chevron.l e_r lr((frak(A)_r)) | r in Phi chevron.r)$ при всех
$a in Phi$ пересекается с $X_a$ по $e_a lr((frak(A)_a))$. Из лемм
@lem:l1982-parabolic-carpet-components, @lem:l1982-parabolic-three-blocks сейчас
вытекает

#lemma[
  Выполнение следующих условий необходимо и достаточно для элементарной
  ковровости подгруппы $M$ группы $Phi(K)$:
  #enum(
    numbering: ru-enum,
    [пересечения $M inter X_r=e_r lr((frak(A)_r))$ порождают $M$;],
    [${frak(A)_r | r in Phi}$ — допустимый элементарный ковёр;],
    [$M inter (U U^-)=(M inter U)(M inter U^-)$.],
  )
] <lem:l1982-parabolic-elementary-carpet-criterion>

При $Phi=A_(n-1)$ подгруппы $U=U(Phi,K)$, $U^-$, $X_r$ можно рассматривать (без
предположения коммутативности кольца $K$), как подгруппы группы $GL_n lr((K))$.
При этом $U=UT_n lr((K))$, $Omega$ состоит из подгрупп
$t_(i j) lr((K))=epsilon+K epsilon_(i j)$, $i!=j$, а соотношения
@eq:l1982-parabolic-elementary-carpet-condition принимают вид
$
  frak(A)_(k m) supset frak(A)_(k l) frak(A)_(l m)
  quad (1<=k,l,m<=n; quad k!=m, quad k!=l, quad l!=m).
$
Напомним, что набор аддитивных подгрупп ${frak(A)_(i j) | 1<=i,j<=n}$ кольца $K$
с условием $frak(A)_(i j) frak(A)_(j m) subset frak(A)_(i m)$ ($1<=i,j,m<=n$)
называют ковром степени $n$ над $K$. Он определяет матричное кольцо
$R(frak(A))=sum_(i,j=1)^n frak(A)_(i j) epsilon_(i j)$; группу $Gamma(frak(A))$
обратимых элементов мультипликативной полугруппы $epsilon+R(frak(A))$ называют
ковровой. Несложно показывается, что
$(Gamma(frak(A)) inter U)(Gamma(frak(A)) inter U^-)
=Gamma(frak(A)) inter (U U^-)$ и поэтому
$lr(chevron.l t_(i j) lr((frak(A)_(i j))) | 1<=i, j<=n ";" quad i!=j chevron.r)$
— элементарно ковровая подгруппа в $GL_n lr((K))$, в силу лемм
@lem:l1982-parabolic-lattice-subgroup,
@lem:l1982-parabolic-elementary-carpet-criterion. Очевидна

#lemma[
  #source(7, printed: 514)Элементарный ковёр
  ${frak(A)_(i j) | 1<=i,j<=n; quad i!=j}$ над $K$ допускает продолжение до
  ковра степени $n$ над $K$ тогда и только тогда, когда
  $frak(A)_(i j) frak(A)_(j i) frak(A)_(i j) subset frak(A)_(i j)$, $i!=j$.
] <lem:l1982-parabolic-carpet-diagonal-extension>

#proof[
  Искомое продолжение получим, доопределяя $frak(A)_(i i)$, $1<=i<=n$, как
  аддитивную подгруппу, порождённую множествами $frak(A)_(i j) frak(A)_(j i)$
  ($1<=j<=n$, $j!=i$). Необходимость очевидна.
]
