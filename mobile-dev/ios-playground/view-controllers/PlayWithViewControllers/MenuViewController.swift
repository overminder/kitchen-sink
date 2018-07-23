//
// Created by Yuxiang JIANG on 7/19/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit


class RootMenuViewController: UIViewController, DispatcherDelegate {
    static let reuseId = "RootMenuViewController.reuseId"

    let tableView = UITableView()

    var viewController: UIViewController? {
        return self
    }

    override func loadView() {
        tableView.dataSource = self
        tableView.delegate = self
        tableView.register(UITableViewCell.self, forCellReuseIdentifier: RootMenuViewController.reuseId)

        view = tableView
    }

    private func item(forIndexPath indexPath: IndexPath) -> DisplayableAction? {
        return menuActions[safe: indexPath.item]
    }

}

extension RootMenuViewController: UITableViewDataSource {
    public func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return menuActions.count
    }

    public func tableView(_ tableView: UITableView, titleForHeaderInSection section: Int) -> String? {
        return "SectionTitle"
    }

    public func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let cell = tableView.dequeueReusableCell(withIdentifier: RootMenuViewController.reuseId, for: indexPath)
        if let item = item(forIndexPath: indexPath) {
            cell.textLabel?.text = item.0
            cell.selectionStyle = .none
        }
        return cell
    }
}

extension RootMenuViewController: UITableViewDelegate {
    public func tableView(_ tableView: UITableView, willSelectRowAt indexPath: IndexPath) -> IndexPath? {
        if let item = item(forIndexPath: indexPath) {
            globalDispatcher.dispatch(item.mkAction?(), delegate: self)
        }
        return indexPath
    }
}
