#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l1982-parabolic-root-isolation>

В применениях теоремы~@th:l1982-parabolic-normal-basis-decomposition к группам
$Phi^L lr((K))$ и $twisted(n, Phi)_sigma lr((K))$ с $B subset U$, $D subset H^L$
выполнимость условия~@eq:l1982-parabolic-extraction-condition зависит, в силу
@eq:l1982-parabolic-diagonal-conjugation, от совокупности значений на корне
$s in Phi$ $K$-характеров группы $L$, переводящих в $1$ заданный корень $r$. Для
доказательства простоты групп $Phi(K)$ над полем $K$ Шевалле выявил случаи,
когда существует пара корней $r,s$ и $K$-характер $chi$ группы $L_1$ такие, что
$chi(r)=1$, $chi(s)!=1$ [@bib:l1982-parabolic-Chevalley1958, §4, лемма 11]. Этот
результат обобщает и усиливает

#lemma[
  Всякий корень приведённой неразложимой системы корней $Phi$ можно перевести
  $K$-характером группы весов $L$, $L_0 subset L subset L_1$, в произвольный
  обратимый элемент $t$ коммутативного кольца $K$; исключением является случай
  $(Phi,L)=(C_l,L_1)$, $l>=1$, когда любой корень можно перевести в $t^2$. Для
  линейно независимых корней $r,s in Phi$ существует $K$-характер $chi$ группы
  $L$ такой, что $chi(r)=1$, $chi(s)=t^d$, где $d$ есть целое число, причём либо
  $1<=d<=rho(Phi)$, либо $L!=L_0$ и $(Phi,d)=(A_2,3)$ или $(D_l,2)$, $l>=3$.
] <lem:l1982-parabolic-root-isolation>

#proof[
  Аддитивная группа $L$, являясь свободной абелевой группой, имеет базы над
  кольцом целых чисел или, кратко, $ZZ$-базы; $K$-характеры группы $L$ можно
  определять значениями элементов $ZZ$-базы. Как и в
  [@bib:l1982-parabolic-Chevalley1958] (см. также
  [@bib:l1982-parabolic-Carter1972, 11.1.3]), при $(Phi,L)!=(C_l,L_1)$, $l>=1$,
  всякий корень $r in Phi$ дополняем до $ZZ$-базы группы $L$. В исключительном
  случае корни записываются в виде $plus.minus 2 epsilon_i$ или
  $plus.minus epsilon_i plus.minus epsilon_j$ ($i<j$), где
  $epsilon_1,epsilon_2,dots,epsilon_l$ — ортонормированный базис евклидова
  пространства $cal(E)$; он является также $ZZ$-базой группы $L_1$
  [@bib:l1982-parabolic-Bourbaki1972, таблица III]. Любые два различных элемента
  $
    alpha,beta in {epsilon_1,epsilon_2,dots,epsilon_l;
      epsilon_i plus.minus epsilon_j,1<=i<j<=l}
  $
  либо сами дополняются до $ZZ$-базы группы $L_1$ элементами $epsilon_i$, либо
  $alpha=epsilon_i plus.minus epsilon_j$, $beta=epsilon_i minus.plus epsilon_j$
  и до $ZZ$-базы дополняема #source(13, printed: 520)пара элементов
  $alpha,(alpha+beta)/2$. Это доказывает случай $(Phi,L)=(C_l,L_1)$ леммы и её
  первое утверждение.

  Далее, $(Phi,L)!=(C_l,L_1)$. В этом случае существует $ZZ$-база группы $L$, в
  которой координатные строки корней $r$ и $s$ образуют матрицу
  $mat(1, 0, 0, dots, 0; m, d, 0, dots, 0)$, $0<=m<d$ (см. также лемму 1
  [@bib:l1982-parabolic-Chevalley1958, §1]). Поэтому для некоторого
  $K$-характера $chi$ группы $L$ имеем $chi(r)=1$, $chi(s)=t^d$. При $m=0$,
  очевидно, имеем $d=1$; случай $(m,d)=(1,2)$ даёт $(s plus.minus r)/2 in L$, и
  поэтому [@bib:l1982-parabolic-Bourbaki1972, следствие на стр. 185] $(r,s)=0$.

  Отметим, что число $d=d(r,s)$ не зависит от выбора $ZZ$-базы в $L$, а группа
  $L$, как и её группа $K$-характеров, не зависит от выбора базиса
  $Pi={p_1,dots,p_l}$ в $Phi$. Группа Вейля $W$ действует транзитивно на корнях
  одинаковой длины, а также на базисах [@bib:l1982-parabolic-Chevalley1958, §1,
  лемма 5; @bib:l1982-parabolic-Bourbaki1972, стр. 187, 191]. Поэтому при
  рассмотрении $d(r,s)$ можно считать, что $r$ есть либо фиксированный короткий
  корень, либо фиксированный длинный корень; равенство $d(r,s)=d(r,-s)$
  позволяет считать, что $s in Phi^+$. Напомним, что порядок фактор-группы
  $L_1/L_0$ равен $l+1,2,2,4,3,2,1,1,1$ соответственно тому, какой из типов
  $A_l,B_l,C_l,D_l,E_6,E_7,E_8,F_4,G_2$ имеет $Phi$. Кроме того, $B_2=C_2$,
  $A_3=D_3$, $A_1=C_1$.

  В соответствии с [@bib:l1982-parabolic-Bourbaki1972, таблицы II, IV],
  $
    Phi^+ lr((D_l))={epsilon_i plus.minus epsilon_j | 1<=i<j<=l},
  $
  $
    Phi^+ lr((B_l))=Phi^+ lr((D_l)) union {epsilon_1,epsilon_2,dots,epsilon_l},
    quad l>=3,
  $
  и в группах $L_1 lr((D_l))$, $L_1 lr((B_l))$ можно выбрать одну и ту же
  $ZZ$-базу
  $epsilon_1,epsilon_2,dots,epsilon_(l-1),omega_l=(1/2)(epsilon_1+epsilon_2+
    dots+epsilon_l)$. Пусть $r=epsilon_1-epsilon_2$ или $epsilon_1$. Если $s$ —
  корень из $Phi^+ lr((B_l))$, то либо абсолютные величины его координат не
  превосходят $1$, либо его последняя координата равна $2$. В обоих случаях
  матрица, составленная из координатных строк корней $r$ и $s$, имеет минор,
  равный $plus.minus 1$ или $plus.minus 2$. Поэтому при $Phi=B_l$,
  $L_0 subset L subset L_1$, а в силу соотношений $Phi(D_l) subset Phi(B_l)$,
  $L_1 lr((D_l))=L_1 lr((B_l)) supset L_0 lr((B_l)) supset L_0 lr((D_l))$, также
  и при $Phi=D_l$, $L_0 subset L subset L_1$, $L!=L_0$, выполняется неравенство
  $d(r,s)<=2$. Равенство здесь достигается; например,
  $d(epsilon_1-epsilon_2,epsilon_1+epsilon_2)=2$.

  #source(14, printed: 521)Докажем, что при $Phi=A_l$ ($l>=4$) и при $Phi=E_l$,
  $l=6$ или $7$, равенство $d(r,s)=1$ выполняется, если $L=L_1$. Пусть
  $
    r=p_l, quad s=sum_(i=1)^l k_i p_i=sum_(j=1)^l m_j q_j in Phi^+.
  $
  Коэффициенты $m_j$ находим из равенств $p_i=sum_(j=1)^l A_(i j) q_j$, где
  $A_(i j)$ — числа Картана; коэффициенты $k_i$ см.
  [@bib:l1982-parabolic-Bourbaki1972, таблицы I, V, VI]. В частности,
  $p_l=-q_(l-1)+2q_l$. Сейчас достаточно показать, что существует $j<l-1$, при
  котором $m_j=plus.minus 1$. Это очевидно, если $k_i<=1$ ($k_i>=0$), $1<=i<=l$,
  в частности, когда $Phi=A_l$ ($l>=4$). Пусть $Phi=E_l$, $l=6$ или $7$, и
  существует $k_i>1$, причём $m_1!=plus.minus 1$. В силу
  [@bib:l1982-parabolic-Bourbaki1972] должны иметь $k_1=1$, $k_3=2$,
  $1<=k_2<=2<=k_4<=l-3$, причём $m_2=2k_2-k_4$, $m_3=-k_1+2k_3-k_4=3-k_4$.
  Отсюда либо $m_2=plus.minus 1$, либо $k_4$ — чётное число и
  $m_3=plus.minus 1$. Итак, $d(r,s)=1$. Таким образом, для указанных $Phi$ корни
  $r,s$ можно дополнить до $ZZ$-базы группы $L_1$, а, следовательно, и до
  $ZZ$-базы группы $L$, $L_0 subset L subset L_1$.

  Пусть $L=L_0$, $s=k_1 p_1+dots+k_l p_l$, $r=p_i$, $i=1$ или $l$ (при
  $rho(Phi)>1$ имеем $|p_1|!=|p_l|$). Тогда $d(r,s)$ — наибольший общий делитель
  чисел $k_j$, $j!=i$, и в силу [@bib:l1982-parabolic-Bourbaki1972, таблицы
  I–IX], $d(r,s)<=rho(Phi)$; равенство достигается при всех $Phi$. Для $Phi=G_2$
  удобно использовать геометрическое представление (например,
  [@bib:l1982-parabolic-Carter1972, стр. 46]). Если хотя бы один из корней
  $r,s in Phi=G_2$ короткий, то $d(r,s)<=2$ и равенство достигается; если же
  $r,s$ — длинные корни, то $d(r,s)=3$. Длинные корни системы $Phi=G_2$ образуют
  систему корней типа $A_2$; при этом $L_1 lr((A_2))=L_0 lr((G_2))$. Таким
  образом, доказан и случай $(Phi,L)=(A_2,L_1)$. Лемма доказана.
]

Для каждого $K$-характера $chi$ группы $L_1 lr((twisted(n, Phi)))$ определим
$K$-характер $chi_xi$ группы $L_1 lr((Phi))$ условием
$chi_xi lr((a))=chi(xi(a))$, $a in L_1 lr((Phi))$, при помощи гомоморфизма
$xi:Phi->twisted(n, Phi)$ (см. лемму~@lem:l1982-parabolic-root-folding). Если
$chi(twisted(n, Phi))$ лежит в подкольце $K_sigma$ элементов кольца $K$,
неподвижных относительно его автоморфизма $x->overline(x)$, то по
лемме~@lem:l1982-parabolic-twisted-automorphism $chi_xi=overline(chi_xi)$ и
$h(chi_xi) in H_sigma lr((K))$. Поэтому
лемму~@lem:l1982-parabolic-root-isolation можно применять и к подгруппе
$H_sigma lr((K))$ группы $twisted(n, Phi)_sigma lr((K))$ при $rho(Phi)=1$. Из
теоремы~@th:l1982-parabolic-normal-basis-decomposition и
лемм~@lem:l1982-parabolic-root-isolation,
@lem:l1982-parabolic-root-folding–@lem:l1982-parabolic-semilocal-bruhat вытекает

#theorem[
  Пусть $A$ — подгруппа группы $Phi^L lr((K))$. Допустим, что группа $K^hash$
  имеет подгруппу $T$, #source(15, printed: 522)удовлетворяющую условиям
  $(k,1)$, $1<=k<=rho(Phi)$ и, когда $L!=L_0$, дополнительному условию $(2.2)$
  при $Phi=C_l$ ($l>=1$), $(3.1)$ при $Phi=A_2$, $(2.1)$ при $Phi=D_l$ ($l>=3$),
  причём $A supset {h(chi) in H^L lr((K)) | chi(L) subset T}$. Если также
  $A supset U^- lr((K))$ и коммутативное кольцо $K$ полулокально (или
  $A subset H^L lr((K)) U(K)$), то подгруппа $A$ совпадает с произведением
  элементарно ковровой подгруппы группы $Phi(K)$ на $A inter H^L lr((K))$ и
  абнормальна в $(A inter H^L lr((K))) Phi(K)$ (соответственно в
  $U(K)(A inter H^L lr((K)))$). Аналогично подгруппа $A$ группы
  $twisted(n, Phi)_sigma^L lr((K))$, $rho(Phi)=1$, $Phi!=A_(2k)$, содержащая
  ${h(chi) in H_sigma^L lr((K)) | chi(L) subset T}$, совпадает с произведением
  элементарно ковровой подгруппы группы $twisted(n, Phi)_sigma lr((K))$ на
  $A inter H_sigma^L lr((K))$ и абнормальна в
  $(A inter H_sigma^L lr((K))) twisted(n, Phi)_sigma lr((K))$ (либо в
  $U_sigma lr((K))(A inter H_sigma^L lr((K)))$), если
  $A supset U_sigma^- lr((K))$ и коммутативное кольцо $K$ полулокально
  (соответственно $A subset U_sigma lr((K)) H_sigma^L lr((K))$), а подгруппа $T$
  группы $K_sigma^hash$ удовлетворяет условию $(2.1)$ и, кроме того, условию
  $(2.2)$ при $Phi=A_(2k+1)$ ($k>=1$), $L!=L_0$, $(3.1)$ при
  $twisted(n, Phi)=twisted(3, D_4)$.
] <th:l1982-parabolic-unipotent-overgroups>

=== #[ ] <sec:l1982-parabolic-comparison>

Понятия ковра и ковровой подгруппы (см.
§~@sec:l1982-parabolic-elementary-carpets) ввёл Ю.~И.~Мерзляков
[@bib:l1982-parabolic-Merzlyakov1964], см. также
[@bib:l1982-parabolic-Kargapolov1977, 16.1.2]. Применяя их при условии
коммутативности кольца $K$ (с другим определением подгруппы $Gamma(frak(A))$),
он ограничивается случаем, когда $frak(A)_(i j)$ — идеалы. Автор рассматривал в
группе $UT_n lr((K))$ над любым кольцом $K$ подгруппы, определяемые строго
значимыми $(n,K)$-слоями [@bib:l1982-parabolic-Levchuk1974]; подгруппы,
определяемые ковром аддитивных подгрупп, выделяются там же следствием
@cor:l1974-parameter-invariants. Обобщая результаты Ньюмана и Райнера
[@bib:l1982-parabolic-Newman1959], Н.~С.~Романовский
[@bib:l1982-parabolic-Romanovskii1971] применил ковры к описанию параболических
подгрупп, а затем, обобщая результаты из [@bib:l1982-parabolic-Romanovskii1971]
и следствие @cor:l1974-triangular-normal из [@bib:l1982-parabolic-Levchuk1974],
понятие ковра — с новым названием «сеть» — использовал З.~И.~Боревич
[@bib:l1982-parabolic-Borevich1976a; @bib:l1982-parabolic-Borevich1976b;
@bib:l1982-parabolic-Borevich1978]. К.~Сузуки [@bib:l1982-parabolic-Suzuki1976;
@bib:l1982-parabolic-Suzuki1977b] распространяет результаты
[@bib:l1982-parabolic-Romanovskii1971] на группу Шевалле $Phi(K)$, выделяя набор
идеалов ${frak(A)_r | r in Phi}$ с условием
$frak(A)_r frak(A)_s subset frak(A)_(r+s)$ ($r,s,r+s in Phi$). Основываясь на
[@bib:l1982-parabolic-Borevich1976a; @bib:l1982-parabolic-Borevich1976b],
Н.~А.~Вавилов [@bib:l1982-parabolic-Vavilov1978b] называет такой набор сетью
идеалов типа $Phi$ и в случае, когда $rho(Phi)=1$, освобождает основной
результат К.~Сузуки от некоторых ограничений на вычетные поля кольца $K$.
Аналогичными методами в [@bib:l1982-parabolic-Vavilov1979a] находятся
параболические подгруппы групп $twisted(2, A_(2k+1)) lr((K))$,
$twisted(2, D_l) lr((K))$, $twisted(2, E_6) lr((K))$ с ограничениями на
полулокальное кольцо $K$ (в частности, $2 in K^hash$ и у кольца $K_sigma$ нет
вычетного поля #source(16, printed: 523)$GF(3)$). Возможность улучшить результат
К.~Сузуки отмечалась в [@bib:l1982-parabolic-Levchuk1979]. Доказанная здесь
теорема~@th:l1982-parabolic-unipotent-overgroups включает как частные случаи
основные результаты [@bib:l1982-parabolic-Suzuki1976;
@bib:l1982-parabolic-Vavilov1978b; @bib:l1982-parabolic-Vavilov1979a;
@bib:l1982-parabolic-Levchuk1979]; с учётом замечания после
леммы~@lem:l1982-parabolic-semilocal-bruhat обобщается и основной результат
[@bib:l1982-parabolic-Suzuki1977b] — теорема 1.4. Выявляется также, что с
коврами Ю.~И.~Мерзлякова более тесно связаны элементарные ковры типа $Phi$. Так
как константа $C_(i j;r s)$ всегда совпадает с одним из чисел $plus.minus 1$,
$plus.minus 2$, $plus.minus 3$, а при $i=j=1$ равна $N_(r s)$
[@bib:l1982-parabolic-Chevalley1958], то из леммы 3
[@bib:l1982-parabolic-Chevalley1958, стр. 8] вытекает

#lemma[
  Всякая сеть аддитивных подгрупп типа $Phi$ над $K$ является элементарным
  ковром; если пересечение $K^hash$ с аддитивной подгруппой, порождённой
  единицей, содержит все константы $N_(r s)$ ($r,s,r+s in Phi$), то верно и
  обратное. Все элементарные ковры идеалов являются сетями, если
  $N_(r s) in K^hash$ ($r,s,r+s in Phi$).
] <lem:l1982-parabolic-nets-and-elementary-carpets>

#example[
  Пусть $Phi=B_2$, $Phi^+={a,b,a+b,2a+b}$. По
  лемме~@lem:l1982-parabolic-carpet-components подгруппа
  $X_a X_(a+b) e_(2a+b) lr((2K))$ группы $Phi(K)$ является элементарно ковровой
  для любого кольца $K$, а сетевой — только при $2K=K$. Для кольца $K=ZZ_4$
  набор идеалов $frak(A)_a=frak(A)_b=K$, $frak(A)_(a+b)=frak(A)_(2a+b)=2K$,
  $frak(A)_r=0$ ($r in Phi^-$) является квазисетью
  [@bib:l1982-parabolic-Vavilov1978b], а элементарным ковром не является.
] <exm:l1982-parabolic-b2-quasinet>

В связи с леммой~@lem:l1982-parabolic-elementary-carpet-criterion возникает
вопрос: какие условия на элементарный ковёр ${frak(A)_r | r in Phi}$ (в терминах
$frak(A)_r$) необходимы и достаточны для его допустимости? По
лемме~@lem:l1982-parabolic-carpet-diagonal-extension элементарный ковёр
${frak(A)_(i j) | 1<=i,j<=n,i!=j}$ степени $n$ допустим, если
$frak(A)_(i j) frak(A)_(j i) frak(A)_(i j) subset frak(A)_(i j)$, $i!=j$. Вместе
с гомоморфизмом $lr(chevron.l t_(12) lr((K)), t_(21) lr((K)) chevron.r)->
lr(chevron.l X_r, X_(-r) chevron.r)$ это даёт следующую лемму.

#lemma[
  Элементарный ковёр ${frak(A)_r | r in Phi}$ аддитивных подгрупп кольца $K$
  допустим, если $frak(A)_r frak(A)_(-r) frak(A)_r subset frak(A)_r$
  ($r in Phi$).
] <lem:l1982-parabolic-admissible-carpet-triple-product>

Конечно, последнее условие выполняется, когда $frak(A)_r$ есть идеалы. Поэтому в
силу леммы~@lem:l1982-parabolic-nets-and-elementary-carpets следствием
леммы~@lem:l1982-parabolic-admissible-carpet-triple-product оказывается основная
теорема 2, а вместе с ней и теоремы 1, 3, 4 работы
[@bib:l1982-parabolic-Vavilov1979b], в которой изучается вопрос построения
аналога ковровой подгруппы в группе Шевалле. Отметим, что доказательство теоремы
2 в [@bib:l1982-parabolic-Vavilov1979b] также основано на переходе от сети
идеалов типа $Phi$ к соответствующему ковру идеалов Ю.~И.~Мерзлякова. Пример
элементарного ковра $frak(A)_(21)={0,1}$, $frak(A)_(12)={0,a}$ степени $2$ над
полем $GF(4)={0,1,a,a+1}$ показывает, что существует допустимый элементарный
ковёр степени $n$, не продолжаемый #source(17, printed: 524)до ковра степени $n$
(этот пример указал автору Я.~Н.~Нужин). Из теоремы Диксона
[@bib:l1982-parabolic-Gorenstein1968, стр. 44] следует, что элементарный ковёр
не обязан быть допустимым.

