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
    # We use os.path.join with '**' and recursive=True for this.
    search_pattern = os.path.join(task_dir, '**', '*.md')
    
    for file_path in glob.glob(search_pattern, recursive=True):
        # Skip files that are already in the 'done' directory to avoid processing them again.
        if os.path.commonpath([file_path, done_dir]) == done_dir:
            continue

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                # Read only the first 5 lines to check for the status.
                for i, line in enumerate(f):
                    if i >= 5:
                        break
                    
                    # Check for "Status: done", ignoring case and leading/trailing whitespace.
                    if line.strip().lower() == "status: done":
                        file_name = os.path.basename(file_path)
                        dest_path = os.path.join(done_dir, file_name)
                        
                        print(f"Archiving '{os.path.relpath(file_path, project_root)}' to '{os.path.relpath(dest_path, project_root)}'")
                        shutil.move(file_path, dest_path)
                        # Once the file is moved, we break the inner loop and continue to the next file.
                        break
        except Exception as e:
            print(f"Error processing file {file_path}: {e}")

if __name__ == "__main__":
    print("Starting to archive completed tasks...")
    archive_done_tasks()
    print("Archiving complete.")
