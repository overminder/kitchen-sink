//
// Created by Yuxiang JIANG on 7/20/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

private func mkSystemFont() -> UIFont {
    return UIFont.systemFont(ofSize: UIFont.systemFontSize)
}

private func boundingSize(height: Int) -> CGSize {
    return CGSize(width: 320, height: height)
}

private struct FancyModel {
    let action: DisplayableAction?
    let height: Int?
    let color: UIColor?

    func rect() -> CGRect {
        // Not really working...
        let bsize = boundingSize(height: height ?? 100)
        if let text = action?.text {
            return (text as NSString).boundingRect(with: bsize, options: .usesLineFragmentOrigin,
                attributes: [NSAttributedStringKey.font: mkSystemFont()], context: nil)
        } else {
            return CGRect(origin: .zero, size: bsize)
        }
    }

    func bindCell(cell: FancyCell) {
        if let action = action {
            let label = UILabel()
            label.text = action.text
            cell.addSubview(label)

            ConstraintSet.fit(label, into: cell)
        }
        if let color = color {
            cell.backgroundColor = color
        }
    }
}

private class FancyCell: UITableViewCell {
    static let reuseId = "FancyCell"

    override var reuseIdentifier: String? {
        return FancyCell.reuseId
    }

    override func prepareForReuse() {
        super.prepareForReuse()

        miscExtRemoveAllSubviews()
    }
}

private let fancyTableItems: [FancyModel] = Array(menuActions.enumerated().map { (ix, elem) -> FancyModel in
    if ix % 2 == 0 {
        return FancyModel(action: elem, height: nil, color: UIColor.yellow)
    } else {
        return FancyModel(action: elem, height: 200, color: nil)
    }
}.map { (m0: FancyModel) -> [FancyModel] in
    let m = FancyModel(action: ("Dummy", nil), height: nil, color: nil)
    return [m0, m, m]
}.joined())

class FancyTableViewController: UIViewController, DispatcherDelegate {
    let tableView = UITableView()

    var viewController: UIViewController? {
        return self
    }

    override func loadView() {
        tableView.dataSource = self
        tableView.delegate = self
        tableView.register(FancyCell.self, forCellReuseIdentifier: FancyCell.reuseId)

        view = tableView
    }

    private func item(forIndexPath indexPath: IndexPath) -> FancyModel? {
        return fancyTableItems[safe: indexPath.item]
    }

}

extension FancyTableViewController: UITableViewDataSource {
    public func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return fancyTableItems.count
    }

    public func tableView(_ tableView: UITableView, titleForHeaderInSection section: Int) -> String? {
        return "SectionTitle"
    }

    public func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let cell = tableView.dequeueReusableCell(withIdentifier: FancyCell.reuseId, for: indexPath)
        if let item = item(forIndexPath: indexPath) {
            cell.selectionStyle = .none
            if let cell = cell as? FancyCell {
                item.bindCell(cell: cell)
            }
        }
        return cell
    }
}

extension FancyTableViewController: UITableViewDelegate {
    public func tableView(_ tableView: UITableView, willSelectRowAt indexPath: IndexPath) -> IndexPath? {
        if let item = item(forIndexPath: indexPath) {
            globalDispatcher.dispatch(item.action?.mkAction?(), delegate: self)
        }
        return indexPath
    }

    public func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        if let item = item(forIndexPath: indexPath) {
            return CGFloat((item.height ?? 100) + 20)
        }
        return 0
    }
}

