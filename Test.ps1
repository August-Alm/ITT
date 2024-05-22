$configFile = Join-Path $PSScriptRoot "test.json"

$config = Get-Content $configFile
  | ConvertFrom-Json

$namn = $config.Namn
$andraNamn = $config.AndraNamn

Write-Host "Namn: $namn"
Write-Host "AndraNamn: $andraNamn"