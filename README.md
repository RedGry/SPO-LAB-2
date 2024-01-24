# СПО - Лабораторная работа №2
## Задание
> Реализовать построение графа потока управления посредством анализа дерева разбора для набора входных файлов. Выполнить анализ собранной информации и сформировать набор файлов с графическим представлением для результатов анализа.

## Вариант
Находится в файле [model](./model)

## Необходимые пакеты
+ bison 3.8.2
+ flex 2.6.4
+ graphviz
+ gcc, g++, gdb

## Запуск проекта на Clion (windows / linux):
1. Настроить себе Clion, чтобы можно было выполнять **Makefile**. Советую использовать Cygwin для винды. Как это сделать: [ссылка](https://www.jetbrains.com/help/clion/quick-tutorial-on-configuring-clion-on-windows.html#Cygwin)
2. Установить себе все необходимые пакеты.
3. Запустить команду `make all_lab2`.
4. Посмотреть результат в созданной директории **out**.