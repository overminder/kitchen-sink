//
// Created by Yuxiang JIANG on 7/21/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit


private let reuseId = "MTCell"

struct LabelCollectionModelMutator {
    private var nextId = 1

    private mutating func genNextId() -> Int {
        let r = nextId
        nextId += 1
        return r
    }

    mutating func mutate(_ coll: inout LabelCollectionModel) {
        coll.sections[0].viewModels.append(LabelViewModel(caption: "intro.\(genNextId())"))
    }
}

class MutableTableViewController: UITableViewController {
    private var coll: LabelCollectionModel = .sample
    private var modelMutator = LabelCollectionModelMutator()

    override func viewDidLoad() {
        super.viewDidLoad()

        tableView.register(UITableViewCell.self, forCellReuseIdentifier: reuseId)
        refreshControl = UIRefreshControl()
        refreshControl?.addTarget(self, action: #selector(refresh), for: .valueChanged)
    }

    @objc
    private func refresh() {
        if refreshControl?.isRefreshing ?? false {
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.5) { [weak self] in
                self?.doRefresh()
            }
        }
    }

    func doRefresh() {
        modelMutator.mutate(&coll)
        tableView.reloadData()
        refreshControl?.endRefreshing()
    }

    private func sectionModel(forSection: Int) -> LabelSectionModel? {
        return coll.sections[safe: forSection]
    }


    private func viewModel(forSection: Int, row: Int) -> LabelViewModel? {
        return sectionModel(forSection: forSection)?.viewModels[safe: row]
    }

    override func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let cell = tableView.dequeueReusableCell(withIdentifier: reuseId, for: indexPath)
        if let vm = viewModel(forSection: indexPath.section, row: indexPath.row) {
            vm.bindTableView(cell)
        }
        return cell
    }

    override func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return sectionModel(forSection: section)?.viewModels.count ?? 0
    }

    override func numberOfSections(in tableView: UITableView) -> Int {
        return coll.sections.count
    }

    override func tableView(_ tableView: UITableView, titleForHeaderInSection section: Int) -> String? {
        return sectionModel(forSection: section)?.sectionHeader
    }

    override func tableView(_ tableView: UITableView, willSelectRowAt indexPath: IndexPath) -> IndexPath? {
        return indexPath
    }
}

