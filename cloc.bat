powershell -Command "dir -Recurse *.v | Get-Content | Measure-Object -Line"
powershell -Command "dir -Recurse Monoidal/*.v | Get-Content | Measure-Object -Line"