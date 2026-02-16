import os
import shutil
import glob

def archive_done_tasks():
    # The script is in 'tools/', so the project root is one level up.
    script_dir = os.path.dirname(os.path.realpath(__file__))
    project_root = os.path.abspath(os.path.join(script_dir, '..'))
    
    task_dir = os.path.join(project_root, 'task')
    done_dir = os.path.join(task_dir, 'done')

    # Create the 'done' directory if it doesn't exist.
    if not os.path.exists(done_dir):
        print(f"Creating directory: {done_dir}")
        os.makedirs(done_dir)

    # Find all .md files recursively under the 'task' directory.
    search_pattern = os.path.join(task_dir, '**', '*.md')
    
    files_to_move = []
    for file_path in glob.glob(search_pattern, recursive=True):
        # Skip files that are already in the 'done' directory.
        if os.path.commonpath([file_path, done_dir]) == done_dir:
            continue
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                for i, line in enumerate(f):
                    if i >= 5:
                        break
                    if line.strip().lower() == "status: done":
                        files_to_move.append(file_path)
                        break
        except Exception as e:
            print(f"Error reading file {file_path}: {e}")

    for file_path in files_to_move:
        try:
            file_name = os.path.basename(file_path)
            dest_path = os.path.join(done_dir, file_name)
            
            print(f"Archiving '{os.path.relpath(file_path, project_root)}' to '{os.path.relpath(dest_path, project_root)}'")
            
            # To work around potential file locking issues, we copy and then delete.
            shutil.copy2(file_path, dest_path)
            os.remove(file_path)

        except Exception as e:
            print(f"Error moving file {file_path}: {e}")

if __name__ == "__main__":
    print("Starting to archive completed tasks...")
    archive_done_tasks()
    print("Archiving complete.")
