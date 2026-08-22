import * as vscode from "vscode";

export interface EnvironmentSymbol {
  name: string;
  class: string;
  detail?: string;
}

export interface EnvironmentFrame {
  label: string;
  symbols: EnvironmentSymbol[];
}

export interface EnvironmentReport {
  capabilities: string[];
  frames: EnvironmentFrame[];
}

export type EnvironmentRequester = (
  uri: string | undefined
) => Promise<EnvironmentReport | undefined>;

export type EnvironmentNode =
  | { type: "capabilities" }
  | { type: "capability"; label: string }
  | { type: "frame"; frame: EnvironmentFrame }
  | { type: "symbol"; symbol: EnvironmentSymbol };

function symbolIcon(symbolClass: string): vscode.ThemeIcon {
  switch (symbolClass) {
    case "operative":
      return new vscode.ThemeIcon("symbol-keyword");
    case "applicative":
      return new vscode.ThemeIcon("symbol-function");
    default:
      return new vscode.ThemeIcon("symbol-variable");
  }
}

/**
 * The environment inspector: capabilities and the frame chain, served by the
 * language server's ironkernel/environment request. Frame structure is
 * host-side by design — the runtime deliberately exposes no parent
 * environments to Kernel code.
 */
export class EnvironmentViewProvider implements vscode.TreeDataProvider<EnvironmentNode> {
  private report: EnvironmentReport | undefined;
  private readonly emitter = new vscode.EventEmitter<EnvironmentNode | undefined | void>();
  readonly onDidChangeTreeData = this.emitter.event;

  constructor(private readonly request: EnvironmentRequester) {}

  async refresh(uri: string | undefined): Promise<void> {
    this.report = await this.request(uri);
    this.emitter.fire();
  }

  getTreeItem(node: EnvironmentNode): vscode.TreeItem {
    switch (node.type) {
      case "capabilities": {
        const count = this.report?.capabilities.length ?? 0;
        const item = new vscode.TreeItem(
          `Capabilities (${count})`,
          count > 0
            ? vscode.TreeItemCollapsibleState.Collapsed
            : vscode.TreeItemCollapsibleState.None
        );
        item.iconPath = new vscode.ThemeIcon("shield");
        item.tooltip =
          count > 0
            ? "Host authority carried by the session environment"
            : "No host authority: the minimal profile";
        return item;
      }
      case "capability": {
        const item = new vscode.TreeItem(node.label, vscode.TreeItemCollapsibleState.None);
        item.iconPath = new vscode.ThemeIcon("key");
        return item;
      }
      case "frame": {
        const item = new vscode.TreeItem(
          node.frame.label,
          node.frame.symbols.length > 0
            ? node.frame.label === "buffer"
              ? vscode.TreeItemCollapsibleState.Expanded
              : vscode.TreeItemCollapsibleState.Collapsed
            : vscode.TreeItemCollapsibleState.None
        );
        item.iconPath = new vscode.ThemeIcon("symbol-namespace");
        item.description = `${node.frame.symbols.length}`;
        return item;
      }
      case "symbol": {
        const item = new vscode.TreeItem(node.symbol.name, vscode.TreeItemCollapsibleState.None);
        item.iconPath = symbolIcon(node.symbol.class);
        item.description = node.symbol.class;
        if (node.symbol.detail) {
          item.tooltip = node.symbol.detail;
        }
        return item;
      }
    }
  }

  getChildren(node?: EnvironmentNode): EnvironmentNode[] {
    if (!this.report) {
      return [];
    }
    if (!node) {
      return [
        { type: "capabilities" },
        ...this.report.frames.map((frame): EnvironmentNode => ({ type: "frame", frame }))
      ];
    }
    switch (node.type) {
      case "capabilities":
        return this.report.capabilities.map((label) => ({ type: "capability", label }));
      case "frame":
        return node.frame.symbols.map((symbol) => ({ type: "symbol", symbol }));
      default:
        return [];
    }
  }
}
