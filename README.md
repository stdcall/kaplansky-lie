# Алгебры Ли и локально компактные группы

И. Капланский.

Перевод с английского Е. А. Горина. Москва: Мир, 1974. Серия «Библиотека
сборника „Математика“». Оригинал: I. Kaplansky, *Lie Algebras and Locally
Compact Groups*, Chicago Lectures in Mathematics, The University of Chicago
Press, 1971.

Первая глава — алгебры Ли: разрешимые, нильпотентные и полупростые алгебры,
подалгебры Картана и геометрическая классификация простых алгебр в
характеристике 0 и характеристике $p$. Вторая глава — решение пятой проблемы
Гильберта: строение локально компактных групп, группы без малых подгрупп,
работы Глисона и Ямабе.

В [релизах](https://github.com/stdcall/kaplansky-lie/releases) — книга с
редакционными примечаниями, отдельный список исправлений опечаток и ошибок
оригинала и контрольные суммы SHA-256.

Для сборки нужны Typst 0.15.1, Typstyle 0.15.1, Tinymist 0.15.10, Python 3.14,
uv и just. Шрифты и их лицензии включены в `assets/fonts`.

```sh
just build
just check
just corrections
just check-sage   # точные вычисления, SageMath
just check-lean   # Lean 4 и mathlib
```

Результаты записываются в `build/`. Математические проверки описаны в
[checks/README.md](checks/README.md), соглашения исходников — в
[CONTRIBUTING.md](CONTRIBUTING.md).
