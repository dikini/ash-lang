# „Начален израз“ означава израза, който задава стойността на променливата.
binding-initializer = Тази променлива изисква стойност от тип `{ $expected }`, но началният израз има тип `{ $found }`.
initializer = Този начален израз има тип `{ $found }`.
binding-annotation = Тази анотация изисква тип `{ $expected }`.
lex-bare-carriage-return = След символ за връщане на каретката трябва да има символ за нов ред (CRLF); самостоятелен символ за нов ред (LF) също е допустим.
lex-byte-order-mark = Изходните файлове на Ash не трябва да съдържат маркер за реда на байтовете (BOM).
lex-unicode-identifier = Имената в Ash използват само ASCII букви, цифри и долни черти.
lex-comment = Ash не поддържа коментари.
lex-negative-literal = Ash не поддържа отрицателни целочислени литерали.
lex-invalid-integer-literal = Целочисленият литерал трябва да е 0 или поредица от ASCII цифри без водеща нула.
lex-invalid-identifier = Името в Ash трябва да започва с ASCII буква или долна черта и да продължава с ASCII букви, цифри или долни черти.
lex-unknown-character = Този символ не може да започва лексикална единица в Ash.
parse-expected =
    { $expected ->
        *[expression] Тук се очаква израз.
        [operand] Тук се очаква операнд.
        [identifier] Тук се очаква име.
        [type] Тук се очаква тип.
        [effect-row] Тук се очаква ред от ефекти.
        [kind] Тук се очаква вид.
        [pattern] Тук се очаква образец.
        [interface-parameter] Тук се очаква типов параметър на интерфейса.
        [interface-method] Тук се очаква сигнатура на метод на интерфейса.
        [effect-operation] Тук се очаква сигнатура на операция на ефекта.
        [interface-application] Тук се очаква прилагане на интерфейс.
        [implementation-method] Тук се очаква уравнение за метод на реализацията.
        [comma] Тук се очаква `,`.
        [left-paren] Тук се очаква `(`.
        [right-paren] Тук се очаква `)`.
        [left-brace] Тук се очаква `{ "{" }`.
        [right-brace] Тук се очаква `{ "}" }`.
        [greater] Тук се очаква `>`.
        [colon] Тук се очаква `:`.
        [equal] Тук се очаква `=`.
        [arrow] Тук се очаква `->`.
        [fat-arrow] Тук се очаква `=>`.
        [line-end] Тук се очаква край на логически ред.
        [end-of-file] Входът трябва да свършва тук.
    }
parse-found =
    { $found ->
        [identifier] Тук има име.
        [uppercase-identifier] Тук има име с начална главна буква.
        [integer] Тук има целочислен литерал.
        [line-end] Тук свършва логически ред.
        [end-of-file] Входът свършва тук.
       *[other] Тук има `{ $found }`.
    }
parse-operand = Операторът изисква десен операнд.
parse-unclosed-group = Тази отваряща скоба няма съответстваща `)`.
parse-repeated-equality = Сравненията за равенство не могат да се свързват във верига без скоби.
parse-recursive-member = Тук се очаква член на групата от рекурсивни свързвания.
parse-unexpected-and = `and` е допустимо само в група от рекурсивни свързвания.
parse-semicolon = Ash не поддържа точки и запетаи.
parse-unexpected-token = Тази лексикална единица не е допустима на това място в граматиката.
parse-recovery = Разборът продължава от това място.
parse-synchronization = Разборът се възобновява на тази граница.
input-invalid-utf8 = `{ $path }` не е валиден изходен файл в UTF-8.
import-target = Неуспехът възникна при обработката на този импорт.
module-root-unavailable = Не може да се използва `{ $path }` като директория за корен за модули `{ $root }`.
module-root-io = Не може да се използва `{ $path }` за корен за модули `{ $root }`: { io-cause }
input-read = Не може да се прочете `{ $path }`: { io-cause }
io-cause = { $kind ->
        [not-found] файлът или директорията не съществува.
        [permission-denied] достъпът е отказан.
        [connection-refused] връзката е отказана.
        [connection-reset] връзката е прекъсната принудително.
        [host-unreachable] хостът е недостъпен.
        [network-unreachable] мрежата е недостъпна.
        [connection-aborted] връзката е прекратена.
        [not-connected] връзката не е установена.
        [addr-in-use] адресът вече се използва.
        [addr-not-available] адресът е недостъпен.
        [network-down] мрежата не работи.
        [broken-pipe] каналът е затворен.
        [already-exists] целевият обект вече съществува.
        [would-block] операцията би блокирала.
        [not-a-directory] компонент от пътя не е директория.
        [is-a-directory] целевият обект е директория.
        [directory-not-empty] директорията не е празна.
        [read-only-filesystem] файловата система е само за четене.
        [stale-network-file-handle] дескрипторът на мрежовия файл вече е невалиден.
        [invalid-input] входен параметър е невалиден.
        [invalid-data] операцията срещна невалидни данни.
        [timed-out] времето за изпълнение на операцията изтече.
        [write-zero] операцията за запис не записа данни.
        [storage-full] хранилището е пълно.
        [not-seekable] файлът не поддържа позициониране.
        [quota-exceeded] квота за ресурс е превишена.
        [file-too-large] файлът надвишава ограничение за размер.
        [resource-busy] ресурсът е зает.
        [executable-file-busy] изпълнимият файл е зает.
        [deadlock] операцията би причинила взаимно блокиране.
        [crosses-devices] операцията пресича граници между файлови системи.
        [too-many-links] файлът има твърде много връзки.
        [invalid-filename] името на файла е невалидно или твърде дълго.
        [argument-list-too-long] списъкът с аргументи е твърде дълъг.
        [interrupted] операцията е прекъсната.
        [unsupported] операцията не се поддържа.
        [unexpected-eof] файлът свърши неочаквано.
        [out-of-memory] заделянето на памет е неуспешно.
        [other] възникна некатегоризирана входно-изходна грешка.
       *[uncategorized] възникна некатегоризирана входно-изходна грешка.
    }
syntax-depth = Разборът на `{ $path }` достигна лимита на компилатора за вложеност от { $limit }.
module-reserved-root = Коренът за модули `{ $root }` е запазен от Ash.
module-duplicate-root = Коренът за модули `{ $root }` е зададен повече от веднъж.
module-invalid-root-name = `{ $root }` не е валиден идентификатор на Ash с малка начална буква за корен за модули.
module-unknown-root = Не е зададен корен за модули с име `{ $root }`.
module-unknown-builtin = Този импорт не посочва модул, предоставен от компилатора.
module-not-found = Импортираният изходен файл `{ $path }` не съществува.
module-import-cycle = Този импорт създава цикъл от зависимости през `{ $path }`.
module-path-escape = Импортираният изходен файл `{ $path }` е извън корен, който трябва да го съдържа.
module-missing-parent = Ash запази път към модул без родителска директория.
module-missing-segments = Ash запази път за импорт без сегменти с имена на модули.
entry-missing-main = Входният модул трябва да дефинира собствен `main`; импортирането му не е достатъчно.
entry-polymorphic = Входната точка `main` не трябва да има типови параметри.
entry-domain = Входната точка `main` трябва да е функция, която приема `Unit`.
entry-effects = Извикването на `main` не трябва да изисква ефекти от извикващия го код.
entry-open-result = Резултатният тип на `main` трябва да е напълно определен, без типови параметри, квантифицирани типове или отворени редове от ефекти.
entry-constrained = Входната точка `main` не трябва да изисква интерфейсни свидетелства от извикващия го код.
entry-module = Това е входният модул.
type-definition-result = Тялото на функцията трябва да връща `{ $expected }`, но връща `{ $found }`.
type-operator-operand = Този оператор изисква операнд от тип `Int`, но този операнд има тип `{ $found }`.
type-argument = Този аргумент на функцията трябва да има тип `{ $expected }`, но има тип `{ $found }`.
type-not-applicable = Този израз не може да бъде извикан: типът му е `{ $found }`, а не функционален тип.
type-equation-signature = Това уравнение изисква функционална сигнатура, но сигнатурата му има тип `{ $found }`.
type-found = Това има тип `{ $found }`.
type-result-annotation = Тази сигнатура изисква резултатен тип `{ $expected }`.
type-operator-requirement = Този оператор изисква операнди от тип `Int`.
type-function-domain = Тази функция изисква аргумент от тип `{ $expected }`.
type-application = Това е обхващащото прилагане на функция.
type-equation-head = Тази глава на уравнение изисква функционална сигнатура.
entry-main = Това е локалната декларация на `main`.
kind-expected-type = Тази позиция изисква завършен тип на стойност (вид `Type`), но видът е `{ $found }`.
kind-not-applicable = Прилаганият тип има вид `{ $found }` и не може да приема типови аргументи.
kind-argument = Този аргумент изисква вид `{ $expected }`, но има вид `{ $found }`.
kind-found = Тук е намерен вид `{ $found }`.
kind-found-declaration = Тази декларация определя вида като `{ $found }`.
kind-required-declaration = Тази декларация изисква аргумент с вид `{ $expected }`.
resolve-unknown-term = Няма име `{ $name }` за стойност в текущия обхват.
resolve-unknown-operation = Избраният ефект не декларира операция с име `{ $name }`.
unresolved-name = Това име не може да бъде разрешено тук.
resolve-duplicate-global = Името `{ $name }` вече е декларирано в този обхват.
resolve-duplicate-type = Името `{ $name }` вече се използва от тип, интерфейс или ефект.
resolve-duplicate-constructor = Конструкторът `{ $name }` вече е деклариран.
resolve-duplicate-alias = Псевдонимът на модул `{ $name }` вече е обвързан.
resolve-duplicate-parameter = Типовият параметър `{ $name }` вече е деклариран в този обхват.
resolve-duplicate-binder = Шаблонът обвързва `{ $name }` повече от веднъж.
resolve-duplicate-recursive-member = Рекурсивната група дефинира `{ $name }` повече от веднъж.
duplicate-name = Това име е в конфликт с по-ранна декларация.
first-declaration = Първа декларация на това име.
first-definition = Пълна по-ранна дефиниция.
resolve-equation-name = Уравнението е с име `{ $name }`, но сигнатурата му декларира `{ $expected }`. Преименувайте уравнението на `{ $expected }`.
resolve-newtype-name = Конструкторът е с име `{ $name }`, но този newtype изисква `{ $expected }`.
resolve-unused-parameter = Явният типов параметър `{ $name }` не се използва в заглавната част на декларацията.
resolve-import-conflict = Името `{ $name }` е в конфликт с обвързване, което вече е в обхвата на този файл.
resolve-opaque-constructor = Конструкторът `{ $name }` принадлежи на непрозрачен тип и не е достъпен тук.
resolve-private-export = Декларацията `{ $name }` е частна за модула, който я дефинира.
resolve-missing-export = Няма достъпна импортирана декларация с име `{ $name }` в това пространство от имена.
resolve-missing-module-alias = Няма псевдоним на модул с име `{ $name }` в текущия обхват.
incorrect-name = Това име не съвпада с изискваното изписване.
unused-parameter = Този параметър не се използва в заглавната част на декларацията.
conflicting-binding = Това обвързване е в конфликт с име в обхвата на целия файл.
inaccessible-name = Това име не е достъпно тук.
required-name-declaration = Тази декларация определя изискваното име.
inaccessible-declaration = Недостъпната декларация е тук.
resolve-unknown-type = Няма тип с име `{ $name }` в текущия обхват.
resolve-unknown-row-parameter = Няма параметър за ред от ефекти с име `{ $name }` в текущия обхват.
resolve-unknown-interface-parameter = Интерфейсът собственик няма параметър с име `{ $name }`.
resolve-unknown-constructor = Няма конструктор с име `{ $name }` в текущия обхват.
resolve-unknown-interface = Няма интерфейс с име `{ $name }` в текущия обхват.
resolve-unknown-effect = Няма ефект с име `{ $name }` в текущия обхват.
resolve-unexported-effect = Избраният модул не експортира ефект с име `{ $name }`.
source-ids = Ash не може да задели нова идентичност за изходния файл `{ $path }`.
projection-recovery = Ash срещна маркери за възстановяване след синтактични грешки при преобразуване на `{ $path }` във вътрешна форма.
projection-malformed = Ash откри несъгласуван вътрешен синтаксис за `{ $path }`: { $cause ->
    [unexpected-finish] затварящо събитие няма отварящо събитие.
    [unclosed-node] синтактичен възел не е затворен.
    [invalid-root-count] синтактичните събития не образуват едно завършено дърво с корен.
    [token-out-of-range] индекс на токен е извън запазения поток от токени.
    [duplicate-token] токен е запазен повече от веднъж.
    [missing-token] токен липсва в синтактичното дърво.
    [token-out-of-order] токените не следват реда в изходния файл.
    [foreign-span] диапазон принадлежи на друг изходен файл.
    [invalid-span] диапазони или маркери за край на входа са несъгласувани.
   *[unexpected-shape] синтактичен възел има неочаквана структура.
    }
source-unrepresentable-span = Ash срещна непредставима дължина на изходен файл или отместване на токен при създаване на диапазон за `{ $path }`.
source-path-limit = Пътят за показване на `{ $path }` надвишава лимита на модела за изходни файлове на Ash.
source-text-limit = Текстът в `{ $path }` надвишава лимита за размер на модела за изходни файлове на Ash.
source-line-limit = `{ $path }` има повече редове, отколкото моделът за изходни файлове на Ash може да представи.
source-column-limit = Ред в `{ $path }` има повече колони, отколкото моделът за изходни файлове на Ash може да представи.
source-range = Ash създаде байтов диапазон { $start }..{ $end } извън { $length } байта на `{ $path }`.
source-foreign-span = Ash използва диапазон от изходен файл { $found }, когато за `{ $path }` се изискваше файл { $expected }.
source-offset = Ash използва байтово отместване { $offset } извън { $length } байта на `{ $path }`.
source-code-point = Ash използва байтово отместване { $offset } вътре в кодова точка в UTF-8 в `{ $path }`.
source-line-state = Вътрешният индекс на редовете на Ash за `{ $path }` е несъгласуван.
module-resource = Ash изчерпа ресурсите за { $resource ->
    [graph-identities] идентичности на графи от модули
    [sources] изходни файлове на модули
    [edges] ребра на импорти
    [path-segments] сегменти на пътища към модули
    [owner-facts] факти за принадлежност на модули
   *[pending-work] чакаща работа по зареждане на модули
    }.
syntax-work = Обработката на `{ $path }` достигна лимита на компилатора за синтактична работа от { $limit }.
