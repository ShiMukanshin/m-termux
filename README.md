# M — универсальный инструмент для Termux

> Двухпанельный файловый менеджер + редактор + куча утилит «всё в одном».
> Только стандартная библиотека Python. Mobile-first.

![version](https://img.shields.io/badge/version-6.1-blue)
![python](https://img.shields.io/badge/python-3.8%2B-green)
![license](https://img.shields.io/badge/license-MIT-lightgrey)
![platform](https://img.shields.io/badge/platform-Termux%20%7C%20Linux-orange)

---

## Что это

`M` — один файл `m.py`, который даёт:

- 🗂 **Двухпанельный файловый менеджер** с вкладками, закладками, скрытыми файлами
- ✏️ **Встроенный редактор** с undo/redo, поиском, заменой, подсветкой через хуки
- ↩️ **Undo/Redo** для всех файловых операций
- 🗑 **Корзину** с восстановлением
- 📦 **Просмотр и распаковку** zip/tar архивов (с защитой от path traversal)
- 📊 **Дашборд** системы (батарея, память, диск, температура, Wi-Fi)
- 🎨 **Подсветку файлов** по расширению
- 🔌 **Систему хуков** для расширения без правки основного кода

Работает в Termux, Linux, macOS, WSL. Никаких зависимостей — только Python 3.8+.

---

## Установка

### Termux (Android)

```bash
pkg update && pkg install python git
git clone https://github.com/<твой-ник>/m.git
cd m
chmod +x m.py
~/m.py
#ОПЦИОНАЛЬНО
mkdir -p ~/bin
ln -s "$PWD/m.py" ~/bin/m
chmod +x ~/bin/m
# если ~/bin не в PATH:
echo 'export PATH="$HOME/bin:$PATH"' >> ~/.bashrc
