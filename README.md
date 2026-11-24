# Trabalho T2 — Métodos Formais (Deque Circular em Dafny)

Implementação e verificação formal de um **Deque Circular** (*Double-Ended Queue*) em **Dafny**, utilizando array com interpretação de fila circular e gerência de frame dinâmico (`Repr`).

**Integrantes:** Giovanna Cruz Castro, Eduarda dos Santos Patricio

---

## Como rodar no GitHub Codespaces

### 1. Instalar o Dafny e o solver Z3

Abra o terminal do Codespace e execute os comandos abaixo:

```bash
# Instala o Dafny globalmente via .NET
dotnet tool install --global dafny

# Adiciona as ferramentas do .NET ao PATH
export PATH="$PATH:$HOME/.dotnet/tools"

# Instala o solver Z3
sudo apt-get update && sudo apt-get install -y z3
```

**Dica:** Para não precisar rodar o `export PATH` toda vez que abrir um novo terminal, adicione-o ao seu `~/.bashrc`:

```bash
echo 'export PATH="$PATH:$HOME/.dotnet/tools"' >> ~/.bashrc
```

### 2. Verificar a prova formal

Valida todas as pré-condições, pós-condições, invariantes e variantes do código:

```bash
dafny verify --solver-path $(which z3) DequeCircular.dfy
```

### 3. Executar os testes unitários (`Main`)

Compila e executa o método `Main`:

```bash
dafny run --solver-path $(which z3) DequeCircular.dfy
```

### (Opcional) Verificação em tempo real no VS Code

1. Abra a aba **Extensions** no Codespace.
2. Instale a extensão oficial **Dafny** (`dafny-lang.ide-vscode`).
3. Abra o arquivo `DequeCircular.dfy` para visualizar o status da verificação direto no editor.